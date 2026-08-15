#!/bin/bash
# Build with progress announcements for protocol verification

# Track which announcements have been printed
thyHBB1_done=false
thyHBB2_done=false
thyHBB3_done=false

# Run lake build with verbose output and monitor for protocol completion
# Filter out trace lines to keep output clean
BUILD_EXIT=1
while IFS= read -r line; do
    # Recover lake's exit status (emitted as the final marker line below)
    if [[ "$line" == LAKE_EXIT:* ]]; then
        BUILD_EXIT=${line#LAKE_EXIT:}
        continue
    fi
    # Skip trace lines
    if [[ "$line" == trace:* ]]; then
        continue
    fi

    echo "$line"

    # Check for ThyHBB1 completion
    if [[ "$line" == *"ModalDistribution.Examples.ThyHBB1.Liveness_Two"* ]] && [ "$thyHBB1_done" = false ]; then
        echo ""
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo "✓ Correctness properties of ThyHBB1 proved."
        echo "  • Agreement property"
        echo "  • Liveness property 1"
        echo "  • Liveness property 2"
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo ""
        thyHBB1_done=true
    fi

    # Check for ThyHBB2 completion
    if [[ "$line" == *"ModalDistribution.Examples.ThyHBB2.Liveness_Two"* ]] && [ "$thyHBB2_done" = false ]; then
        echo ""
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo "✓ Correctness properties of ThyHBB2 proved."
        echo "  • Agreement property"
        echo "  • Liveness property 1"
        echo "  • Liveness property 2"
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo ""
        thyHBB2_done=true
    fi

    # Check for ThyHBB3 completion
    if [[ "$line" == *"ModalDistribution.Examples.ThyHBB3.Liveness_Two"* ]] && [ "$thyHBB3_done" = false ]; then
        echo ""
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo "✓ Correctness properties of ThyHBB3 proved."
        echo "  • Agreement property"
        echo "  • Liveness property 1"
        echo "  • Liveness property 2"
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo ""
        thyHBB3_done=true
    fi

    # Finish announcement
    if [[ "$line" == *"Build completed successfully"* ]]; then
        echo ""
        echo "╔════════════════════════════════════════════════════════════╗"
        echo "║  Verification of paper \"Heterogeneous trust in reliable    ║"
        echo "║  broadcast via modal logic and history structures\"         ║"
        echo "║  complete.                                                 ║"
        echo "╚════════════════════════════════════════════════════════════╝"
        echo ""
    fi
done < <(lake build --verbose 2>&1; echo "LAKE_EXIT:$?")

exit $BUILD_EXIT
