#!/usr/bin/env python3
"""Fail-closed audit of all explicitly listed #print axioms outputs.
This is a log check, not a substitute for Lean or independent replay.
"""
import pathlib
import re
import sys

EXPECTED = {
    'MOR34.valid_iff_count_prefixes',
    'MOR34.invalid_iff_count_violation',
    'MOR34.support_iff_tight_prefix',
    'MOR34.support_iff_count_epigraph',

    'MOR34.affineSpan_of_augment_mem',
    'MOR34.rational_selectedSpan_to_real',
    'MOR34.countReal_affineSpan_of_rational_span',
    'MOR34.real_count_basis_from_linear_oracle',

    'MOR34.finite_rational_integer_multiple',
    'MOR34.count_functional_coefficients',
    'MOR34.integer_form_of_functional',
    'MOR34.bounded_integer_forms_exist',
    'MOR34.bounded_integer_forms_family',
    'MOR34.count_basis_from_linear_oracle',

    'MOR34.firstWitness_some',
    'MOR34.firstWitness_none',
    'MOR34.firstWitness_calls_le',
    'MOR34.positiveQuery_iff',
    'MOR34.negativeQuery_iff',
    'MOR34.outsideQueries_length',
    'MOR34.linearSpanOracle_spec',
    'MOR34.linearSpanOracle_calls_le',
    'MOR34.linearBasisCalls_le',
    'MOR34.linear_count_basis_correct',

    'MOR34.basisSearch_card',
    'MOR34.basisSearch_calls_le',
    'MOR34.basisSearch_subset',
    'MOR34.selectedSpan_insert_strict',
    'MOR34.basisSearch_spans',
    'MOR34.basisSearch_from_empty',
    'MOR34.countBasisSearch_correct',

    'MOR34.row_parity_iff',
    'MOR34.exact_parity_linear_count_encoding',

    'MOR34.pickCoeff_sum',
    'MOR34.prefixLine_rational_iff',
    'MOR34.countRows_iff',
    'MOR34.countRow_card',
    'MOR34.exact_linear_count_encoding',

    'MOR34.integerCountBounds_encode',
    'MOR34.decodeCounts_bounded',
    'MOR34.encode_decodeCounts',
    'MOR34.decode_encodeCounts',
    'MOR34.tight_prefix_epigraph',
    'MOR34.restricted_count_epigraph',
    'MOR34.restricted_linear_epigraph',
    'MOR34.count_parity_substitution',
    'MOR34.parity_restricted_epigraph',
    'MOR34.epigraph_variable_count',

    'MOR34.prefixCost_shift',
    'MOR34.prefixLine_le',
    'MOR34.prefixCost_succ',
    'MOR34.prefixLine_attained',
    'MOR34.prefix_epigraph_iff',
    'MOR34.weightSum_prefixCost',
    'MOR34.prefix_feasible_epigraph',

    'MOR34.adjacentEdge_card',
    'MOR34.retainedRowIndex_card',
    'MOR34.small_retained_matrix',

    'MOR34.retained_row_cast',
    'MOR34.retained_row_span',
    'MOR34.retained_matrix_real_rank',
    'MOR34.retained_matrix_rational_rank',

    'MOR34.selected_dimension',
    'MOR34.small_selected_dimension',

    'MOR34.square_matrix_rank_map',
    'MOR34.rational_matrix_rank',
    'MOR34.integer_matrix_rank',

    'MOR34.augmentedSpan_anchor',
    'MOR34.augment_anchor_disjoint',
    'MOR34.augmentedSpan_finrank',

    'MOR34.selectionFinset_coe',
    'MOR34.selectionFinset_card',
    'MOR34.small_selected_span',

    'MOR34.small_cellBasisSelection_exists',
    'MOR34.countReal_injective',
    'MOR34.finite_count_affine_basis',
    'MOR34.cellBasisSelection_exists',

    'MOR34.selectedPoints_tight',
    'MOR34.selectedPoints_quotient_spans',
    'MOR34.selected_augmented_span',

    'MOR34.augment_mem_of_affineSpan',
    'MOR34.zero_vectorSpan_le_augmentedSpan',
    'MOR34.augmented_span_lift',

    'MOR34.adjacent_path_difference_mem',
    'MOR34.adjacentDirectionSpan_eq_exchange',
    'MOR34.adjacentDirectionSpan_eq_ker',

    'MOR34.affine_on_set_span_image',
    'MOR34.actual_cell_span_image',

    'MOR34.cellCondition_unique',
    'MOR34.parity_cell_cover',
    'MOR34.cell_index_card',
    'MOR34.parity_cell_decomposition',
    'MOR34.tight_has_parity',

    'MOR34.tightParity_profile',
    'MOR34.parityExtrema_exists',
    'MOR34.cell_bounds',
    'MOR34.actual_cell_slopes',
    'MOR34.actual_cell_affine',

    'MOR34.prefix_sum_increment',
    'MOR34.component_prefix_sum',
    'MOR34.prefix_affine_on_box',

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
