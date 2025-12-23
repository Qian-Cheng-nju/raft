#!/bin/bash
################################################################################
# Model Check Configuration Script - etcdraft_progress
# Modify the parameters below to control model checking behavior
################################################################################

# ============================================================================
# Configurable Parameters - Modify Here!
# ============================================================================

MEMORY="2G"

# Number of threads (auto detect, or specify a number like 4, 8, 16)
WORKERS="auto"

# Timeout (minutes), 0 means no limit
TIMEOUT_MINUTES=60

# State depth limit (0 means no limit)
# Suggestion: 20-30 can be completed in a reasonable time
MAX_DEPTH=25

# Enable symmetry optimization (true/false)
# Note: Symmetry may cause some errors to be ignored, use with caution
ENABLE_SYMMETRY=false

# Checkpoint interval (minutes) - save progress periodically
CHECKPOINT_MINUTES=10

# Output log file
LOG_FILE="mc_progress_$(date +%Y%m%d_%H%M%S).log"

# TLC parameter files
SPEC_FILE="MCetcdraft_progress.tla"
CONFIG_FILE="MCetcdraft_progress.cfg"

# ============================================================================
# Script logic below, generally no need to modify
# ============================================================================

# Color output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${GREEN}================================${NC}"
echo -e "${GREEN}Model Check Launch Configuration${NC}"
echo -e "${GREEN}================================${NC}"
echo "Memory Limit:     $MEMORY"
echo "Worker Threads:     $WORKERS"
echo "Timeout:     $TIMEOUT_MINUTES minutes"
echo "Depth Limit:     $MAX_DEPTH"
echo "Symmetry Optimization:   $ENABLE_SYMMETRY"
echo "Checkpoint Interval:   $CHECKPOINT_MINUTES minutes"
echo "Log File:     $LOG_FILE"
echo -e "${GREEN}================================${NC}"

# Build TLC command
TLC_CMD="java -XX:+UseParallelGC -Xmx${MEMORY} -Xms${MEMORY}"
TLC_CMD="$TLC_CMD -cp ../../../../lib/tla2tools.jar:../../../../lib/CommunityModules-deps.jar"
TLC_CMD="$TLC_CMD tlc2.TLC"

# Add worker threads
TLC_CMD="$TLC_CMD -workers $WORKERS"

# Add checkpoints
if [ $CHECKPOINT_MINUTES -gt 0 ]; then
    TLC_CMD="$TLC_CMD -checkpoint $CHECKPOINT_MINUTES"
fi

# Add depth limit
if [ $MAX_DEPTH -gt 0 ]; then
    TLC_CMD="$TLC_CMD -depth $MAX_DEPTH"
fi

# Add timeout
if [ $TIMEOUT_MINUTES -gt 0 ]; then
    TIMEOUT_SECONDS=$((TIMEOUT_MINUTES * 60))
    TLC_CMD="timeout ${TIMEOUT_SECONDS}s $TLC_CMD"
fi

# Add config and spec files
TLC_CMD="$TLC_CMD -config $CONFIG_FILE $SPEC_FILE"

echo -e "${YELLOW}Executing Command:${NC}"
echo "$TLC_CMD"
echo ""
echo -e "${GREEN}Starting Model Check...${NC}"
echo ""

# Execute command and log output
eval $TLC_CMD 2>&1 | tee $LOG_FILE

# Check exit status
EXIT_CODE=${PIPESTATUS[0]}

echo ""
echo -e "${GREEN}================================${NC}"
if [ $EXIT_CODE -eq 0 ]; then
    echo -e "${GREEN}✓ Model check completed, no errors found${NC}"
elif [ $EXIT_CODE -eq 124 ]; then
    echo -e "${YELLOW}⚠ Model check timed out${NC}"
elif [ $EXIT_CODE -eq 12 ]; then
    echo -e "${YELLOW}⚠ Invariant violation found!${NC}"
    echo -e "${YELLOW}Please check log: $LOG_FILE${NC}"
else
    echo -e "${YELLOW}⚠ Model check exited abnormally (exit code: $EXIT_CODE)${NC}"
fi
echo -e "${GREEN}================================${NC}"

exit $EXIT_CODE