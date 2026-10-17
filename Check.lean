import MOR34

-- Each named theorem must have only allowed standard axiom dependencies.
-- Successful run evidence is recorded in docs/ACCEPTANCE.json.
#print axioms MOR34.one_feasible_of_pair_sum
#print axioms MOR34.balanced_values_are_tight
#print axioms MOR34.interior_cut_arithmetic

-- These commands display proposition specifications, not proof terms:
#check MOR34.BalancedSplitGoal
#check MOR34.PairingAtCutGoal
#check MOR34.InteriorExchangeGoal

-- Paper interfaces; #check alone is not a proof.
#check MOR34.PaperInterface.PrefixMinimality
#check MOR34.PaperInterface.IntervalExchange
#check MOR34.PaperInterface.ParityInterior

#print axioms MOR34.balancedSplit

#print axioms MOR34.mem_classPrefix
#print axioms MOR34.card_classPrefix
#print axioms MOR34.classPrefix_mono
#print axioms MOR34.mem_assemble
#print axioms MOR34.counts_assemble
#print axioms MOR34.prefixSet_assemble
#print axioms MOR34.split_prescribed

#print axioms MOR34.classPairSpec_comm
#print axioms MOR34.ordered_pair_prescribed
#print axioms MOR34.class_pair
#print axioms MOR34.class_pair_cross
#print axioms MOR34.pairingAtCut

#print axioms MOR34.tight_swap
#print axioms MOR34.intervalExchange
#print axioms MOR34.sum_eq_indicator
#print axioms MOR34.repartition_sum
#print axioms MOR34.candidateValue_counts
#print axioms MOR34.one_tight_of_repartition
#print axioms MOR34.adjacent_of_crosses
#print axioms MOR34.interiorExchange

#print axioms MOR34.exchangeConnected_refl
#print axioms MOR34.exchangeConnected_symm
#print axioms MOR34.exchangeConnected_trans
#print axioms MOR34.path_crosses_cut
#print axioms MOR34.adjacent_chain
#print axioms MOR34.connected_forces_cut
#print axioms MOR34.adjacent_cut_exchange
#print axioms MOR34.cuts_give_connected
#print axioms MOR34.connected_iff_cuts
#print axioms MOR34.component_interval
#print axioms MOR34.parity_interior_connected

#print axioms MOR34.mem_classSlice
#print axioms MOR34.assemble_classSlice
#print axioms MOR34.counts_classSlice
#print axioms MOR34.counts_bounded
#print axioms MOR34.counts_prefixSet
#print axioms MOR34.sum_assemble
#print axioms MOR34.orderEmbedding_index_le
#print axioms MOR34.classPrefix_map
#print axioms MOR34.classPrefix_minimal
#print axioms MOR34.prefixMinimality
#print axioms MOR34.prefix_tight

#print axioms MOR34.fiberSumMap_unit
#print axioms MOR34.unitVector_expansion
#print axioms MOR34.fiberDifferenceSpan_le_ker
#print axioms MOR34.anchor_sum_zero
#print axioms MOR34.fiberDifferenceSpan_eq_ker_of_section
#print axioms MOR34.fiberDifferenceSpan_eq_ker

#print axioms MOR34.path_difference_mem
#print axioms MOR34.edgeDifferenceSpan_eq_ker
#print axioms MOR34.globalExchangeAdj_symm
#print axioms MOR34.exchangeDirectionSpan_eq_global
#print axioms MOR34.exchangeDirectionSpan_eq_ker

#print axioms MOR34.fiberSumMap_surjective
#print axioms MOR34.componentCountMap_surjective
#print axioms MOR34.exchangeDirectionSpan_finrank

#print axioms MOR34.pointVector_swap_difference
#print axioms MOR34.exchangeDirectionSpan_le_tightVectorSpan
#print axioms MOR34.finrank_subspace_map
#print axioms MOR34.tight_dimension_quotient

#print axioms MOR34.sum_eq_of_cross_equal
#print axioms MOR34.pointVector_sum_units
#print axioms MOR34.componentCountMap_pointVector
#print axioms MOR34.prefix_component_class_sum
#print axioms MOR34.componentCountMap_prefix
#print axioms MOR34.tight_image_eq_prefix_image

#print axioms MOR34.global_connected_class_iff
#print axioms MOR34.componentLabel_eq_iff_class_connected
#print axioms MOR34.componentLabel_interval

#print axioms MOR34.prefix_sum_increment
#print axioms MOR34.component_prefix_sum
#print axioms MOR34.prefix_affine_on_box

#print axioms MOR34.tightParity_profile
#print axioms MOR34.parityExtrema_exists
#print axioms MOR34.cell_bounds
#print axioms MOR34.actual_cell_slopes
#print axioms MOR34.actual_cell_affine

#print axioms MOR34.parity_cell_cover
#print axioms MOR34.cell_index_card
#print axioms MOR34.parity_cell_decomposition
#print axioms MOR34.tight_has_parity

#print axioms MOR34.cellCondition_unique

#print axioms MOR34.affine_on_set_span_image
#print axioms MOR34.actual_cell_span_image

#print axioms MOR34.adjacent_path_difference_mem
#print axioms MOR34.adjacentDirectionSpan_eq_exchange
#print axioms MOR34.adjacentDirectionSpan_eq_ker

#print axioms MOR34.augment_mem_of_affineSpan
#print axioms MOR34.zero_vectorSpan_le_augmentedSpan
#print axioms MOR34.augmented_span_lift

#print axioms MOR34.selectedPoints_tight
#print axioms MOR34.selectedPoints_quotient_spans
#print axioms MOR34.selected_augmented_span

#print axioms MOR34.countReal_injective
#print axioms MOR34.finite_count_affine_basis
#print axioms MOR34.cellBasisSelection_exists

#print axioms MOR34.small_cellBasisSelection_exists

#print axioms MOR34.selectionFinset_coe
#print axioms MOR34.selectionFinset_card
#print axioms MOR34.small_selected_span

#print axioms MOR34.augmentedSpan_anchor
#print axioms MOR34.augment_anchor_disjoint
#print axioms MOR34.augmentedSpan_finrank

#print axioms MOR34.square_matrix_rank_map
#print axioms MOR34.rational_matrix_rank
#print axioms MOR34.integer_matrix_rank

#print axioms MOR34.selected_dimension
#print axioms MOR34.small_selected_dimension

#print axioms MOR34.retained_row_cast
#print axioms MOR34.retained_row_span
#print axioms MOR34.retained_matrix_real_rank
#print axioms MOR34.retained_matrix_rational_rank

#print axioms MOR34.adjacentEdge_card
#print axioms MOR34.retainedRowIndex_card
#print axioms MOR34.small_retained_matrix

#print axioms MOR34.prefixCost_shift
#print axioms MOR34.prefixLine_le
#print axioms MOR34.prefixCost_succ
#print axioms MOR34.prefixLine_attained
#print axioms MOR34.prefix_epigraph_iff
#print axioms MOR34.weightSum_prefixCost
#print axioms MOR34.prefix_feasible_epigraph

#print axioms MOR34.integerCountBounds_encode
#print axioms MOR34.decodeCounts_bounded
#print axioms MOR34.encode_decodeCounts
#print axioms MOR34.decode_encodeCounts
#print axioms MOR34.tight_prefix_epigraph
#print axioms MOR34.restricted_count_epigraph
#print axioms MOR34.restricted_linear_epigraph
#print axioms MOR34.count_parity_substitution
#print axioms MOR34.parity_restricted_epigraph
#print axioms MOR34.epigraph_variable_count

#print axioms MOR34.pickCoeff_sum
#print axioms MOR34.prefixLine_rational_iff
#print axioms MOR34.countRows_iff
#print axioms MOR34.countRow_card
#print axioms MOR34.exact_linear_count_encoding

#print axioms MOR34.row_parity_iff
#print axioms MOR34.exact_parity_linear_count_encoding

#print axioms MOR34.basisSearch_card
#print axioms MOR34.basisSearch_calls_le
#print axioms MOR34.basisSearch_subset
#print axioms MOR34.selectedSpan_insert_strict
#print axioms MOR34.basisSearch_spans
#print axioms MOR34.basisSearch_from_empty
#print axioms MOR34.countBasisSearch_correct

#print axioms MOR34.firstWitness_some
#print axioms MOR34.firstWitness_none
#print axioms MOR34.firstWitness_calls_le
#print axioms MOR34.positiveQuery_iff
#print axioms MOR34.negativeQuery_iff
#print axioms MOR34.outsideQueries_length
#print axioms MOR34.linearSpanOracle_spec
#print axioms MOR34.linearSpanOracle_calls_le
#print axioms MOR34.linearBasisCalls_le
#print axioms MOR34.linear_count_basis_correct

#print axioms MOR34.finite_rational_integer_multiple
#print axioms MOR34.count_functional_coefficients
#print axioms MOR34.integer_form_of_functional
#print axioms MOR34.bounded_integer_forms_exist
#print axioms MOR34.bounded_integer_forms_family
#print axioms MOR34.count_basis_from_linear_oracle

#print axioms MOR34.affineSpan_of_augment_mem
#print axioms MOR34.rational_selectedSpan_to_real
#print axioms MOR34.countReal_affineSpan_of_rational_span
#print axioms MOR34.real_count_basis_from_linear_oracle

#print axioms MOR34.valid_iff_count_prefixes
#print axioms MOR34.invalid_iff_count_violation
#print axioms MOR34.support_iff_tight_prefix
#print axioms MOR34.support_iff_count_epigraph

#print axioms MOR34.basisSearch_independent
#print axioms MOR34.rational_row_independent
#print axioms MOR34.rational_augmented_independent_to_real
#print axioms MOR34.affineIndependent_of_augmented
#print axioms MOR34.real_count_search_independent

#print axioms MOR34.restrictionIndices_map
#print axioms MOR34.restrictionIndices_card
#print axioms MOR34.restrictedPrefix_subset
#print axioms MOR34.restrictedPrefix_card
#print axioms MOR34.restrictedPrefix_minimal
#print axioms MOR34.restrictedPrefix_cost

#print axioms MOR34.pairAllowed_card
#print axioms MOR34.forcedPairPrefix_pattern
#print axioms MOR34.forcedPairPrefix_card
#print axioms MOR34.forcedPairPrefix_minimal
#print axioms MOR34.forcedPairPrefix_cost

#print axioms MOR34.prefix_epigraph_all_sizes
#print axioms MOR34.forcedPairPrefix_epigraph

#print axioms MOR34.real_affine_basis_from_linear_oracle

#print axioms MOR34.forcedSet_pattern
#print axioms MOR34.counts_forcedSet
#print axioms MOR34.forced_count_bounds
#print axioms MOR34.forcedSet_minimal
#print axioms MOR34.exchange_iff_forced_counts
#print axioms MOR34.forced_feasible_epigraph
#print axioms MOR34.exchange_iff_forced_epigraph

#print axioms MOR34.oracle_cell_basis_selection

#print axioms MOR34.descendingSearch_calls_le
#print axioms MOR34.descendingSearch_none
#print axioms MOR34.descendingSearch_max
#print axioms MOR34.descendingSearch_exists

#print axioms MOR34.coordinateLower_iff
#print axioms MOR34.coordinateUpper_iff
#print axioms MOR34.maximumThreshold_spec
#print axioms MOR34.minimumThreshold_spec
#print axioms MOR34.maximumSearch_spec
#print axioms MOR34.minimumSearch_spec
#print axioms MOR34.maximumSearch_exists
#print axioms MOR34.minimumSearch_exists
#print axioms MOR34.extremaSearchCalls_le

#print axioms MOR34.maximumWitness_result
#print axioms MOR34.minimumWitness_result
#print axioms MOR34.searchedParityExtrema_lower_result
#print axioms MOR34.searchedParityExtrema_upper_result
#print axioms MOR34.all_parity_extrema_calls_le

#print axioms MOR34.cellCoordinateQueries_iff
#print axioms MOR34.cellQueries_iff
#print axioms MOR34.cellQueries_length
#print axioms MOR34.restrictedQueryOracle_spec
#print axioms MOR34.parityCellOracle_spec
#print axioms MOR34.unrestrictedQueryOracle_spec

#print axioms MOR34.queryRestrictions_iff
#print axioms MOR34.parityRows_decode
#print axioms MOR34.parityRows_exists_iff
#print axioms MOR34.parityListSolver_spec

#print axioms MOR34.rowBaseOracle_spec
#print axioms MOR34.rowCellOracle_spec
#print axioms MOR34.row_solver_cell_selection
#print axioms MOR34.row_solver_retained_matrix

#print axioms MOR34.feasibleRows_iff
#print axioms MOR34.violationInequality_iff
#print axioms MOR34.violationRows_iff
#print axioms MOR34.feasibleEpigraph_decode
#print axioms MOR34.invalid_iff_violation_rows
#print axioms MOR34.violationRow_card

#print axioms MOR34.violationRows_witness
#print axioms MOR34.violationSolver_none_iff
#print axioms MOR34.parityList_mem
#print axioms MOR34.parityList_length
#print axioms MOR34.supportSearch_some
#print axioms MOR34.supportSearch_none_iff
#print axioms MOR34.supportSearch_calls_le
#print axioms MOR34.recognitionBranch_correct
#print axioms MOR34.feasiblePointSet_zero
#print axioms MOR34.feasiblePointSet_unit
#print axioms MOR34.feasiblePointSet_vectorSpan
#print axioms MOR34.feasiblePointSet_affineSpan
#print axioms MOR34.feasiblePointSet_finrank
#print axioms MOR34.rowCellCalls_le
#print axioms MOR34.all_rowCellCalls_le
#print axioms MOR34.rowSearchCalls_le
#print axioms MOR34.cell_solver_row_count
#print axioms MOR34.integerRow_iff
#print axioms MOR34.integerPick_sum
#print axioms MOR34.forcedSlopeRow_iff
#print axioms MOR34.forcedEmptyRow_iff
#print axioms MOR34.forcedSlopeRow_counts
#print axioms MOR34.integerForcedEpigraph_encode
#print axioms MOR34.forcedOrdinaryRow_iff
#print axioms MOR34.forcedRows_iff
#print axioms MOR34.exchange_iff_forced_rows
#print axioms MOR34.forcedRow_card
#print axioms MOR34.forcedRows_witness
#print axioms MOR34.exchangeWitness_some
#print axioms MOR34.exchangeWitness_none_iff
#print axioms MOR34.exchangeDecision_iff
#print axioms MOR34.computedEdges_mem
#print axioms MOR34.adjacentPair_card
#print axioms MOR34.computedEdges_card
#print axioms MOR34.computedEdges_span
#print axioms MOR34.computedMatrix_eq_submatrix
#print axioms MOR34.computed_matrix_rank
#print axioms MOR34.computedRowIndex_card
#print axioms MOR34.computed_edge_has_witness
#print axioms MOR34.computedEdgeWitness_result
#print axioms MOR34.computedEdgeWitness_pair
#print axioms MOR34.knapsackPolytope_affineSpan
#print axioms MOR34.knapsackPolytope_finrank

#print axioms MOR34.returnedSets_tight
#print axioms MOR34.returnedPointSet_subset
#print axioms MOR34.selectedPoints_returned
#print axioms MOR34.returnedSets_card
#print axioms MOR34.returned_direction_span
#print axioms MOR34.returned_augmented_span
#print axioms MOR34.returned_affineSpan
#print axioms MOR34.returned_affine_basis_exists

#print axioms MOR34.linear_bound_convexHull
#print axioms MOR34.supporting_hull_eq
#print axioms MOR34.supporting_level_extreme

#print axioms MOR34.candidateLinear_point
#print axioms MOR34.valid_linear_bound
#print axioms MOR34.valid_polytope_bound
#print axioms MOR34.tightPointSet_level
#print axioms MOR34.candidateFace_eq_hull
#print axioms MOR34.candidateFace_convex
#print axioms MOR34.candidateFace_extreme
#print axioms MOR34.candidateFace_nonempty_iff
#print axioms MOR34.candidateFace_affineSpan
#print axioms MOR34.candidateFace_vectorSpan
#print axioms MOR34.candidate_facet_iff_dimension
#print axioms MOR34.candidate_facet_iff_computed_rank

#print axioms MOR34.executedCell_eq_selectionCell
#print axioms MOR34.executedSelection_eq

#print axioms MOR34.executedParity_eq_cells
