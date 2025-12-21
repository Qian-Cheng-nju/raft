#!/bin/bash

# Script to clean up auto-generated TLA+ trace files
# Only deletes files matching pattern: *TTrace_*.tla and *TTrace_*.bin

TLA_DIR="."

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${YELLOW}=== TLA+ Trace Files Cleanup Script ===${NC}"
echo ""

# Check if directory exists
if [ ! -d "$TLA_DIR" ]; then
    echo -e "${RED}Error: Directory $TLA_DIR does not exist${NC}"
    exit 1
fi

# Find all matching files
echo "Searching for trace files in $TLA_DIR..."
FILES=$(find "$TLA_DIR" -maxdepth 1 -type f \( -name "*TTrace_*.tla" -o -name "*TTrace_*.bin" \))

# Count files
COUNT=$(echo "$FILES" | grep -v "^$" | wc -l)

if [ $COUNT -eq 0 ]; then
    echo -e "${GREEN}No trace files found. Directory is already clean.${NC}"
    exit 0
fi

echo -e "${YELLOW}Found $COUNT trace files to delete:${NC}"
echo ""
echo "$FILES"
echo ""

# Ask for confirmation
read -p "Do you want to delete these files? (yes/no): " CONFIRM

if [ "$CONFIRM" = "yes" ] || [ "$CONFIRM" = "y" ]; then
    echo ""
    echo "Deleting files..."

    # Delete files
    find "$TLA_DIR" -maxdepth 1 -type f \( -name "*TTrace_*.tla" -o -name "*TTrace_*.bin" \) -delete

    echo -e "${GREEN}✓ Successfully deleted $COUNT trace files${NC}"
else
    echo -e "${YELLOW}Cleanup cancelled.${NC}"
    exit 0
fi
