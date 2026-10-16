#!/usr/bin/env python3
"""Fail-closed audit of all explicitly listed #print axioms outputs.
This is a log check, not a substitute for Lean or independent replay.
"""
import pathlib
import re
import sys

EXPECTED = {
    'MOR34.global_connected_class_iff',
    'MOR34.componentLabel_eq_iff_class_connected',
    'MOR34.componentLabel_interval',

    'MOR34.sum_eq_of_cross_equal',
    'MOR34.pointVector_sum_units',
    'MOR34.componentCountMap_pointVector',
    'MOR34.prefix_component_class_sum',
    'MOR34.componentCountMap_prefix',
    'MOR34.tight_image_eq_prefix_image',

    'MOR34.pointVector_swap_difference',
    'MOR34.exchangeDirectionSpan_le_tightVectorSpan',
    'MOR34.finrank_subspace_map',
    'MOR34.tight_dimension_quotient',

    'MOR34.fiberSumMap_surjective',
    'MOR34.componentCountMap_surjective',
    'MOR34.exchangeDirectionSpan_finrank',

    'MOR34.path_difference_mem',
    'MOR34.edgeDifferenceSpan_eq_ker',
    'MOR34.globalExchangeAdj_symm',
    'MOR34.exchangeDirectionSpan_eq_global',
    'MOR34.exchangeDirectionSpan_eq_ker',

    'MOR34.fiberSumMap_unit',
    'MOR34.unitVector_expansion',
    'MOR34.fiberDifferenceSpan_le_ker',
    'MOR34.anchor_sum_zero',
    'MOR34.fiberDifferenceSpan_eq_ker_of_section',
    'MOR34.fiberDifferenceSpan_eq_ker',

    'MOR34.mem_classSlice',
    'MOR34.assemble_classSlice',
    'MOR34.counts_classSlice',
    'MOR34.counts_bounded',
    'MOR34.counts_prefixSet',
    'MOR34.sum_assemble',
    'MOR34.orderEmbedding_index_le',
    'MOR34.classPrefix_map',
    'MOR34.classPrefix_minimal',
    'MOR34.prefixMinimality',
    'MOR34.prefix_tight',

    'MOR34.exchangeConnected_refl',
    'MOR34.exchangeConnected_symm',
    'MOR34.exchangeConnected_trans',
    'MOR34.path_crosses_cut',
    'MOR34.adjacent_chain',
    'MOR34.connected_forces_cut',
    'MOR34.adjacent_cut_exchange',
    'MOR34.cuts_give_connected',
    'MOR34.connected_iff_cuts',
    'MOR34.component_interval',
    'MOR34.parity_interior_connected',

    'MOR34.tight_swap',
    'MOR34.intervalExchange',
    'MOR34.sum_eq_indicator',
    'MOR34.repartition_sum',
    'MOR34.candidateValue_counts',
    'MOR34.one_tight_of_repartition',
    'MOR34.adjacent_of_crosses',
    'MOR34.interiorExchange',

    'MOR34.classPairSpec_comm',
    'MOR34.ordered_pair_prescribed',
    'MOR34.class_pair',
    'MOR34.class_pair_cross',
    'MOR34.pairingAtCut',

    'MOR34.mem_classPrefix',
    'MOR34.card_classPrefix',
    'MOR34.classPrefix_mono',
    'MOR34.mem_assemble',
    'MOR34.counts_assemble',
    'MOR34.prefixSet_assemble',
    'MOR34.split_prescribed',

    'MOR34.balancedSplit',
    'MOR34.one_feasible_of_pair_sum',
    'MOR34.balanced_values_are_tight',
    'MOR34.interior_cut_arithmetic',
}
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}

def audit(text):
    seen = set()
    for name in EXPECTED:
        quoted = re.escape(name)
        empty = re.search(r"['‘]?" + quoted + r"['’]? does not depend on any axioms", text)
        nonempty = re.search(r"['‘]?" + quoted + r"['’]? depends on axioms:\s*\[([^\]]*)\]", text)
        if empty:
            seen.add(name)
        elif nonempty:
            actual = {a.strip() for a in nonempty.group(1).split(',') if a.strip()}
            if not actual <= ALLOWED:
                raise ValueError(f'{name}: non-allowlisted dependencies: {sorted(actual - ALLOWED)}')
            seen.add(name)
        else:
            raise ValueError(f'Missing or unrecognized axiom output for {name}')
    if 'sorryAx' in text:
        raise ValueError('sorryAx appears in audit output')
    return seen

if __name__ == '__main__':
    try:
        checked = audit(pathlib.Path(sys.argv[1]).read_text())
    except (ValueError, OSError, IndexError) as e:
        print(f'REJECTED: {e}', file=sys.stderr)
        sys.exit(1)
    print('Allowed axiom dependencies for:', ', '.join(sorted(checked)))
