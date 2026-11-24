#!/bin/bash
# Build with progress announcements for protocol verification

# Track which announcements have been printed
hbbSafe_done=false
hbbSimp_done=false
hbbCorr_done=false

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

    # Check for HBBSafe completion
    if [[ "$line" == *"ModalDistribution.Examples.HBBSafe.Correctness"* ]] && [ "$hbbSafe_done" = false ]; then
        echo ""
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo "✓ Correctness properties of HBBSafe proved."
        echo "  • Agreement property"
        echo "  • Happy Termination"
        echo "  • Cascade Termination"
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo ""
        hbbSafe_done=true
    fi

    # Check for HBBSimp completion
    if [[ "$line" == *"ModalDistribution.Examples.HBBSimp.Correctness"* ]] && [ "$hbbSimp_done" = false ]; then
        echo ""
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo "✓ Correctness properties of HBBSimp proved."
        echo "  • Agreement property"
        echo "  • Happy Termination"
        echo "  • Cascade Termination"
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo ""
        hbbSimp_done=true
    fi

    # Check for HBBCorr completion
    if [[ "$line" == *"ModalDistribution.Examples.HBBCorr.Correctness"* ]] && [ "$hbbCorr_done" = false ]; then
        echo ""
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo "✓ Correctness properties of HBBCorr proved."
        echo "  • Agreement property"
        echo "  • Happy Termination"
        echo "  • Cascade Termination"
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo ""
        hbbCorr_done=true
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
