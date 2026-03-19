#!/bin/bash

# Loop through TBD indices
TBD_list=(147 181 287 363 365 366)

prev_i=0
for i in "${TBD_list[@]}"; do
    echo "=========================================="
    echo "Processing proofnet-${i}.lean"
    echo "=========================================="
    
    # Update the prompt file with the current index
    sed -i "s|proofnet-${prev_i}\.lean|proofnet-${i}.lean|g" solve_prompt.txt

    # Execute the claude code command
    claude --dangerously-skip-permissions \
    --verbose \
    --output-format stream-json \
    --model global.anthropic.claude-opus-4-6-v1 \
    -p "$(cat solve_prompt.txt)"

    # Optional sleep to alleviate rate limit
    echo ""
    sleep_minutes=0
    echo "Sleeping for ${sleep_minutes} minutes..."
    sleep $((sleep_minutes * 60))
    echo ""

    # Store current index as previous for next iteration
    prev_i=$i
done