package raft

import (
	"testing"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestJointConsensusSafetyBug demonstrates a potential safety violation in etcd raft's
// joint consensus implementation.
//
// The bug: EnterJoint() allows config changes where old and new configs don't have
// quorum overlap. When changing from {1,2,3} to {3}, the config change entry is
// committed using the OLD config (needs 2 of {1,2,3}). If nodes 1 and 2 form the
// quorum (without node 3), and then both crash, node 3 becomes the sole survivor
// but doesn't have the "committed" entries.
//
// Root cause: EnterJoint() doesn't check for quorum overlap between old and new configs.
// doc.go:267-270 states "old and new configurations are guaranteed to overlap" but
// this guarantee is not enforced in EnterJoint().
//
// The safety violation:
//   - Old config {1,2,3}: quorums are {1,2}, {1,3}, {2,3}
//   - New config {3}: quorum is {3}
//   - {1,2} ∩ {3} = ∅ (no overlap!)
//   - Entries committed by {1,2} are not present on node 3
//   - If nodes 1,2 crash, committed entries are lost
func TestJointConsensusSafetyBug(t *testing.T) {
	// Step 1: Create a 3-node network
	nt := newNetwork(nil, nil, nil)

	// Step 2: Elect node 1 as leader
	nt.send(pb.Message{From: 1, To: 1, Type: pb.MsgHup})

	lead := nt.peers[1].(*raft)
	require.Equal(t, StateLeader, lead.state, "Node 1 should be leader")
	t.Logf("Node 1 elected as leader in term %d", lead.Term)

	// Verify initial config: {1, 2, 3}
	require.Equal(t, []uint64{1, 2, 3}, lead.trk.VoterNodes())
	t.Logf("Initial config: voters=%v", lead.trk.VoterNodes())

	// Step 3: Isolate node 3 - it won't receive any messages
	nt.isolate(3)
	t.Log("Node 3 isolated from the network")

	node3 := nt.peers[3].(*raft)
	node3LastIndexBefore := node3.raftLog.lastIndex()
	t.Logf("Node 3 lastIndex before isolation: %d", node3LastIndexBefore)

	// Step 4: Propose some entries that will be committed with OLD config
	// These entries will be replicated to nodes 1 and 2, but NOT to node 3
	// Committed using old config: only needs 2 of {1,2,3}, so nodes 1+2 suffice
	for i := 0; i < 3; i++ {
		nt.send(pb.Message{
			From:    1,
			To:      1,
			Type:    pb.MsgProp,
			Entries: []pb.Entry{{Data: []byte("data-before-confchange")}},
		})
	}

	t.Logf("After proposing entries: lead.committed=%d, lead.lastIndex=%d",
		lead.raftLog.committed, lead.raftLog.lastIndex())

	// Verify node 3 didn't receive these entries
	require.Equal(t, node3LastIndexBefore, node3.raftLog.lastIndex(),
		"Node 3 should not have received new entries while isolated")

	// Step 5: Propose a joint config change to remove nodes 1 and 2
	// This config change entry is ALSO committed using OLD config (nodes 1+2)
	// Result: joint config ⟨{3}, {1,2,3}⟩
	cc := pb.ConfChangeV2{
		Changes: []pb.ConfChangeSingle{
			{Type: pb.ConfChangeRemoveNode, NodeID: 1},
			{Type: pb.ConfChangeRemoveNode, NodeID: 2},
		},
	}
	ccType, ccData, err := pb.MarshalConfChange(cc)
	require.NoError(t, err)

	nt.send(pb.Message{
		From:    1,
		To:      1,
		Type:    pb.MsgProp,
		Entries: []pb.Entry{{Type: ccType, Data: ccData}},
	})

	t.Logf("After proposing config change: lead.committed=%d", lead.raftLog.committed)
	t.Logf("Config change entry at index %d", lead.raftLog.lastIndex())

	// Step 6: Apply the config change on nodes 1 and 2, then leave joint
	lead.applyConfChange(cc)
	node2 := nt.peers[2].(*raft)
	node2.applyConfChange(cc)

	t.Logf("After applying config change (joint config):")
	t.Logf("  incoming=%v, outgoing=%v",
		lead.trk.Config.Voters[0], lead.trk.Config.Voters[1])

	// Verify we're in joint config
	require.True(t, len(lead.trk.Config.Voters[1]) > 0, "Should be in joint config")

	// Leave joint config
	lead.applyConfChange(pb.ConfChangeV2{}) // Empty means leave joint
	node2.applyConfChange(pb.ConfChangeV2{})

	t.Logf("After leaving joint config:")
	t.Logf("  Final config: voters=%v", lead.trk.VoterNodes())

	// Now the config should be just {3}
	require.Equal(t, []uint64{3}, lead.trk.VoterNodes(),
		"After leave-joint, only node 3 should be a voter")

	// Step 7: Verify the bug - committed entries are missing on node 3
	committedOnMajority := lead.raftLog.committed
	node3LastIndex := node3.raftLog.lastIndex()

	t.Logf("")
	t.Logf("=== BUG DEMONSTRATION ===")
	t.Logf("Node 1 (leader): committed=%d, lastIndex=%d",
		lead.raftLog.committed, lead.raftLog.lastIndex())
	t.Logf("Node 2: committed=%d, lastIndex=%d",
		node2.raftLog.committed, node2.raftLog.lastIndex())
	t.Logf("Node 3: committed=%d, lastIndex=%d",
		node3.raftLog.committed, node3.raftLog.lastIndex())
	t.Logf("")
	t.Logf("Entries committed on nodes 1,2: up to index %d", committedOnMajority)
	t.Logf("Entries on node 3: up to index %d", node3LastIndex)
	t.Logf("Missing entries on node 3: %d", committedOnMajority-node3LastIndex)
	t.Logf("")
	t.Logf("If nodes 1 and 2 crash now:")
	t.Logf("  - Node 3 is the sole survivor")
	t.Logf("  - Node 3 can elect itself (it's the only voter in config {3})")
	t.Logf("  - But node 3 doesn't have %d 'committed' entries!", committedOnMajority-node3LastIndex)
	t.Logf("  - These entries would be LOST - safety violation!")

	// Assert that the bug exists
	require.Less(t, node3LastIndex, committedOnMajority,
		"BUG CONFIRMED: Node 3 (sole remaining voter) is missing committed entries")
}
