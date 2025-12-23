#!/bin/bash
################################################################################
# Run model check in background - simple wrapper script
################################################################################

cd /home/ubuntu/specula/data/repositories/raft/tla

echo "Starting model check in background..."
echo "Process output will be saved to nohup.out"
echo ""

nohup ./run_model_check.sh > nohup.out 2>&1 &

PID=$!
echo "✓ Model check started in background!"
echo "  Process ID: $PID"
echo ""
echo "Common Commands:"
echo "  View real-time log:    tail -f nohup.out"
echo "  View process status:    ps aux | grep $PID"
echo "  Stop process:        kill $PID"
echo "  Force stop:        kill -9 $PID"
echo ""
echo "Log file location: /home/ubuntu/specula/data/repositories/raft/tla/nohup.out"