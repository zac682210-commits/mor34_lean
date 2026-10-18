import MOR34.ViolationConstructionCost
import MOR34.ForcedConstructionCost
import MOR34.ReturnedFamilyCost
import MOR34.CountConstructionCost
import MOR34.IntegerConstructionTrace
import MOR34.NormalBitCost
import MOR34.AggregateArithmeticCost
import MOR34.StoredEdgeWitnesses
import MOR34.NormalArithmeticCost
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

#print axioms MOR34.computedRecognition_correct
#print axioms MOR34.correct_output_facet
#print axioms MOR34.computedRecognition_facet

#print axioms MOR34.weighted_support_equality

#print axioms MOR34.finiteSpanOracle_spec
#print axioms MOR34.finite_basis_search
#print axioms MOR34.outside_iff_rank_increases
#print axioms MOR34.finite_rank_basis_search

#print axioms MOR34.binaryPointMatrix_cast
#print axioms MOR34.binaryPointMatrix_rank
#print axioms MOR34.binaryBasisSearch_correct
#print axioms MOR34.searched_returned_basis

#print axioms MOR34.tight_basis_card
#print axioms MOR34.searched_returned_basis_card
#print axioms MOR34.facet_returned_basis_card

#print axioms MOR34.builtSelection_exists
#print axioms MOR34.normalizedPipeline_correct

#print axioms MOR34.codimensionOneFace_ne
#print axioms MOR34.tightPointSet_candidate
#print axioms MOR34.zero_candidate_all_tight
#print axioms MOR34.zero_candidate_valid
#print axioms MOR34.zero_candidate_not_facet
#print axioms MOR34.valid_empty_not_facet

#print axioms MOR34.integer_det_bound
#print axioms MOR34.integer_cramer_bound
#print axioms MOR34.cramerNormal_kernel
#print axioms MOR34.cramerNormal_nonzero
#print axioms MOR34.cramerNormal_bound

#print axioms MOR34.pivotNormal_kernel
#print axioms MOR34.pivotNormal_bound
#print axioms MOR34.pivotNormal_independent
#print axioms MOR34.factorial_power_bound

#print axioms MOR34.pivotNormal_mem_ker
#print axioms MOR34.pivot_kernel_free_injective
#print axioms MOR34.pivotNormals_span

#print axioms MOR34.finiteBasisRankCalls_le
#print axioms MOR34.returned_basis_rank_calls

#print axioms MOR34.positiveCandidateValues_image
#print axioms MOR34.positiveCandidateValues_card
#print axioms MOR34.zeroClass_card_le_one
#print axioms MOR34.coefficient_class_parameter_bound
#print axioms MOR34.coefficient_classes_le_items

#print axioms MOR34.magnitudeBits_le_of_power_bound
#print axioms MOR34.pivotNormal_magnitudeBits
#print axioms MOR34.pivotNormal_logarithmic_bits

#print axioms MOR34.correct_output_dimension
#print axioms MOR34.normalizedPipeline_dimension

#print axioms MOR34.independent_rows_pivot_minor

#print axioms MOR34.columnNormal_pairing
#print axioms MOR34.integerRowSpan_iff
#print axioms MOR34.column_cramer_pair
#print axioms MOR34.columnNormals_describe

#print axioms MOR34.injective_coordinate_sum_bound
#print axioms MOR34.columnNormal_bound
#print axioms MOR34.columnNormal_uniform_bound

#print axioms MOR34.independent_rows_pivot_columns
#print axioms MOR34.independent_integer_rows_pivot
#print axioms MOR34.bounded_matrix_normals

#print axioms MOR34.augmentedCountRow_cast
#print axioms MOR34.countMatrix_span_iff
#print axioms MOR34.vectorIntegerForm_pairing
#print axioms MOR34.bounded_count_forms_exist

#print axioms MOR34.countRadius_pos
#print axioms MOR34.countRadius_bounds
#print axioms MOR34.countRadius_le
#print axioms MOR34.normalCoefficientBound_mono
#print axioms MOR34.boundedCountForms_spec
#print axioms MOR34.boundedCountForms_length
#print axioms MOR34.boundedCountForms_bound
#print axioms MOR34.normalCoefficient_magnitudeBits

#print axioms MOR34.countSearch_forms_bounded
#print axioms MOR34.boundedCellSelection_basis
#print axioms MOR34.boundedCellSelection_small
#print axioms MOR34.boundedCellSelection_query_calls
#print axioms MOR34.class_size_le_items
#print axioms MOR34.boundedCellSelection_query_bounds

#print axioms MOR34.boundedPipeline_correct

#print axioms MOR34.mem_allFinFunctions
#print axioms MOR34.allFinFunctions_length
#print axioms MOR34.pivotSearch_sound
#print axioms MOR34.pivotSearch_complete
#print axioms MOR34.pivotSearch_calls

#print axioms MOR34.positiveQuery_bound
#print axioms MOR34.negativeQuery_bound
#print axioms MOR34.outsideQueries_bound
#print axioms MOR34.query_parity_row
#print axioms MOR34.query_parity_bound

#print axioms MOR34.boundedPipeline_dimension
#print axioms MOR34.boundedPipeline_facet
#print axioms MOR34.boundedCellSelection_executed

#print axioms MOR34.boundedCountForms_bits
#print axioms MOR34.boundedCountQueries_bound
#print axioms MOR34.boundedParityQueries_bound

#print axioms MOR34.sortItems_class
#print axioms MOR34.sortGrouped_wellFormed
#print axioms MOR34.sortGrouped_weightSum
#print axioms MOR34.sortGrouped_candidateValue
#print axioms MOR34.sortGrouped_feasible
#print axioms MOR34.sortGrouped_tight
#print axioms MOR34.sortGrouped_valid

#print axioms MOR34.normalized_model_exists

#print axioms MOR34.relabel_weight_sum
#print axioms MOR34.relabel_candidate_sum
#print axioms MOR34.relabel_feasible
#print axioms MOR34.relabel_tight
#print axioms MOR34.relabel_valid

#print axioms MOR34.relabel_pointVector
#print axioms MOR34.relabel_tightPointSet
#print axioms MOR34.relabel_tight_finrank

#print axioms MOR34.relabel_positive_values
#print axioms MOR34.raw_parameter_bound
#print axioms MOR34.raw_classes_le_items

#print axioms MOR34.prefixCost_abs_bound
#print axioms MOR34.prefixIntercept_abs_bound
#print axioms MOR34.shiftedPrefixIntercept_abs_bound

#print axioms MOR34.relabel_tight_nonempty
#print axioms MOR34.relabel_signed_dimension

#print axioms MOR34.boundedPipeline_raw_dimension

#print axioms MOR34.rawCandidateLinear_point
#print axioms MOR34.raw_valid_linear_bound
#print axioms MOR34.rawTightPointSet_level
#print axioms MOR34.rawCandidateFace_eq_hull
#print axioms MOR34.rawCandidateFace_convex
#print axioms MOR34.rawCandidateFace_extreme
#print axioms MOR34.rawCandidateFace_nonempty
#print axioms MOR34.rawCandidateFace_vectorSpan
#print axioms MOR34.relabel_feasiblePointSet
#print axioms MOR34.relabel_knapsackPolytope
#print axioms MOR34.relabel_candidateFace
#print axioms MOR34.relabel_polytope_finrank
#print axioms MOR34.relabel_face_finrank
#print axioms MOR34.relabel_geometric_facet
#print axioms MOR34.relabel_definesFacet

#print axioms MOR34.relabelBasis_card
#print axioms MOR34.relabelBasis_points
#print axioms MOR34.relabelBasis_independent
#print axioms MOR34.relabelBasis_tight
#print axioms MOR34.relabelBasis_affineSpan

#print axioms MOR34.relabelDecision_correct
#print axioms MOR34.relabelOutput_correct
#print axioms MOR34.raw_correct_output_facet
#print axioms MOR34.relabelDecision_dimension
#print axioms MOR34.rawPipeline_correct
#print axioms MOR34.rawPipeline_facet
#print axioms MOR34.rawPipeline_dimension

#print axioms MOR34.rawNormalization_exists
#print axioms MOR34.rawNormalization_correct
#print axioms MOR34.rawNormalization_parameter
#print axioms MOR34.rawNormalization_facet
#print axioms MOR34.rawNormalization_dimension
#print axioms MOR34.original_input_output_contract

#print axioms MOR34.integerRow_bounded
#print axioms MOR34.integerRow_bound_mono
#print axioms MOR34.integerPick_abs_bound
#print axioms MOR34.integerRow_withParity
#print axioms MOR34.integerRow_parity_bounded
#print axioms MOR34.queryRow_integer_bounded
#print axioms MOR34.signedIntegerBits_bound
#print axioms MOR34.integerRowBits_bound
#print axioms MOR34.bounded_row_encoding_exists

#print axioms MOR34.countRow_integer_bounded
#print axioms MOR34.parityRows_integer_bounded

#print axioms MOR34.forcedOrdinaryRow_integer_bounded
#print axioms MOR34.forcedSlopeRow_integer_bounded
#print axioms MOR34.forcedEmptyRow_integer_bounded
#print axioms MOR34.forcedRows_integer_bounded

#print axioms MOR34.feasibleRow_as_countRow
#print axioms MOR34.feasibleRows_integer_bounded
#print axioms MOR34.violationInequality_integer_bounded
#print axioms MOR34.violationRows_integer_bounded

#print axioms MOR34.integerQuery_bound_mono
#print axioms MOR34.coordinateLower_bound
#print axioms MOR34.coordinateUpper_bound
#print axioms MOR34.cellCoordinateQueries_bound
#print axioms MOR34.cellQueries_bound
#print axioms MOR34.cell_normal_queries_bound
#print axioms MOR34.cell_normal_parity_rows_bounded

#print axioms MOR34.laplaceDet_correct
#print axioms MOR34.laplaceArithmeticBudget_bound
#print axioms MOR34.exactPivotSearch_sound
#print axioms MOR34.exactPivotSearch_complete
#print axioms MOR34.exactPivotSearch_calls
#print axioms MOR34.laplaceDet_bound

#print axioms MOR34.rawNormalization_magnitude
#print axioms MOR34.rawNormalization_class_size
#print axioms MOR34.original_forced_rows_bounded
#print axioms MOR34.original_violation_rows_bounded
#print axioms MOR34.original_parity_rows_bounded

#print axioms MOR34.tracedLaplaceDet_value
#print axioms MOR34.tracedLaplaceDet_cost
#print axioms MOR34.tracedLaplaceDet_correct_and_cost

#print axioms MOR34.normalRadius_cast
#print axioms MOR34.normalRadius_power_bound
#print axioms MOR34.uniformRowRadius_power_bound
#print axioms MOR34.uniformRow_signed_bits
#print axioms MOR34.cellRow_uniform_bound

#print axioms MOR34.integerRowBits_uniform
#print axioms MOR34.uniform_row_payload
#print axioms MOR34.uniform_system_payload
#print axioms MOR34.cell_system_payload

#print axioms MOR34.searchStates_of_containment
#print axioms MOR34.cellSearch_payload_states
#print axioms MOR34.boundedPipeline_payload_states

#print axioms MOR34.laplaceTerm_abs_bound
#print axioms MOR34.laplace_partial_sum_bound
#print axioms MOR34.laplace_partial_sum_bits

#print axioms MOR34.basicRow_uniform_bound
#print axioms MOR34.forced_system_payload
#print axioms MOR34.violation_system_payload
#print axioms MOR34.firstWitnessCharge_bound
#print axioms MOR34.pivotDetCharge_bound
#print axioms MOR34.exactPivotDetCharge_bound
#print axioms MOR34.selected_rows_span_of_checks
#print axioms MOR34.checked_candidate_describes
#print axioms MOR34.normal_candidate_exists
#print axioms MOR34.concreteColumnNormal_eq
#print axioms MOR34.mem_normalSearchKeys
#print axioms MOR34.tryNormalKey_spec
#print axioms MOR34.matrixNormalSearch_exists
#print axioms MOR34.matrixNormalSearch_isSome
#print axioms MOR34.computedMatrixNormals_spec
#print axioms MOR34.orderedCounts_mem
#print axioms MOR34.orderedCounts_length
#print axioms MOR34.finAugmentedCount_cast
#print axioms MOR34.orderedCountMatrix_span
#print axioms MOR34.finVectorIntegerForm_pairing
#print axioms MOR34.computedCountForms_spec
#print axioms MOR34.computedCountForms_length
#print axioms MOR34.computedCountForms_bound
#print axioms MOR34.computedSearch_forms_bounded
#print axioms MOR34.computedCellSelection_basis
#print axioms MOR34.computedCellSelection_small
#print axioms MOR34.computedCellSelection_query_calls
#print axioms MOR34.computedCellSelection_query_bounds
#print axioms MOR34.computedNormalPipeline_correct
#print axioms MOR34.computedNormalPipeline_dimension
#print axioms MOR34.computedNormalPipeline_facet
#print axioms MOR34.computedCellSelection_executed
#print axioms MOR34.computedRawPipeline_correct
#print axioms MOR34.computedRawPipeline_facet
#print axioms MOR34.computed_original_input_output_contract
#print axioms MOR34.flatMap_length_bound
#print axioms MOR34.normalSearchKeys_length_bound
#print axioms MOR34.matrixNormalSearch_calls
#print axioms MOR34.computedCountForms_search_calls
#print axioms MOR34.searchStates_card
#print axioms MOR34.computedCountForms_search_states
#print axioms MOR34.computedCountForms_bits
#print axioms MOR34.forms_cell_queries_bound
#print axioms MOR34.forms_cell_system_payload
#print axioms MOR34.computedCellSearch_payload_states
#print axioms MOR34.computedNormalPipeline_payload_states
#print axioms MOR34.normalBasisCandidateCalls_bound
#print axioms MOR34.computedCellSelection_normal_checks
#print axioms MOR34.binarySetKey_injective
#print axioms MOR34.orderedBinarySets_mem
#print axioms MOR34.orderedBinarySets_length
#print axioms MOR34.computedParityFamily_eq
#print axioms MOR34.computedSelectionFamily_eq
#print axioms MOR34.computedReturnedSets_eq
#print axioms MOR34.computedReturnedBasis_correct
#print axioms MOR34.executableNormalizedPipeline_correct
#print axioms MOR34.executableNormalizedPipeline_facet
#print axioms MOR34.executableRawPipeline_correct
#print axioms MOR34.executableRawPipeline_facet
#print axioms MOR34.executable_normalized_original_output_contract
#print axioms MOR34.concreteColumnNormal_bound
#print axioms MOR34.normalCheck_term_bound
#print axioms MOR34.normalCheck_partial_sum_bound
#print axioms MOR34.normalCheck_partial_sum_bits
#print axioms MOR34.executableNormalizedPipeline_dimension
#print axioms MOR34.executableParityList_mem
#print axioms MOR34.executableParityList_length
#print axioms MOR34.executableSupportSearch_some
#print axioms MOR34.executableSupportSearch_none_iff
#print axioms MOR34.executableSupportSearch_calls_le
#print axioms MOR34.executableRecognitionBranch_correct
#print axioms MOR34.executable_original_input_output_contract
#print axioms MOR34.executable_normalization_parameter
#print axioms MOR34.materializeFin_apply
#print axioms MOR34.materializeFin_eq
#print axioms MOR34.storedParityExtrema_eq
#print axioms MOR34.executableRawPipeline_dimension
#print axioms MOR34.smallSigns_coordinate
#print axioms MOR34.smallSigns_difference
#print axioms MOR34.smallSigns_positive
#print axioms MOR34.smallSigns_nonnegative
#print axioms MOR34.smallSigns_zero
#print axioms MOR34.smallSigns_order
#print axioms MOR34.smallSigns_equal
#print axioms MOR34.binarySignTest_norm
#print axioms MOR34.binarySignTest_dot
#print axioms MOR34.compression_subset_sign
#print axioms MOR34.compression_subset_le
#print axioms MOR34.compression_subset_eq
#print axioms MOR34.compression_feasible
#print axioms MOR34.compression_tight
#print axioms MOR34.compression_valid
#print axioms MOR34.compression_tightPointSet
#print axioms MOR34.compression_polytope
#print axioms MOR34.compression_face
#print axioms MOR34.compression_facet
#print axioms MOR34.compression_signedDimension
#print axioms MOR34.compression_hypotheses
#print axioms MOR34.compression_decision
#print axioms MOR34.compression_output
#print axioms MOR34.image_card_of_equal_fibers
#print axioms MOR34.positive_values_as_image
#print axioms MOR34.compression_positive_parameter
#print axioms MOR34.compression_all_classes
#print axioms MOR34.compression_coefficient_order
#print axioms MOR34.compression_coefficient_zero
#print axioms MOR34.compressed_original_output_contract
#print axioms MOR34.image_card_le_bucket_card
#print axioms MOR34.varyingClassComponents_card
#print axioms MOR34.varyingComponents_card
#print axioms MOR34.parityComponentGenerators_card
#print axioms MOR34.parityComponentGenerators_span
#print axioms MOR34.oneParityComponentGenerators_card
#print axioms MOR34.allParityComponentGenerators_card
#print axioms MOR34.quotient_prefix_mem_component_generators
#print axioms MOR34.quotient_augmented_span_le_component_generators
#print axioms MOR34.quotient_augmented_dimension_bound
#print axioms MOR34.facet_component_bound
#print axioms MOR34.compressionRadius_power_bound
#print axioms MOR34.compressed_integer_bits
#print axioms MOR34.compressed_payload_bound
#print axioms MOR34.compression_cost_substitution

#print axioms MOR34.clog_two_le_input
#print axioms MOR34.uniformRowBits_polynomial
#print axioms MOR34.dense_query_payload_polynomial
#print axioms MOR34.cell_payload_polynomial
#print axioms MOR34.forced_payload_polynomial
#print axioms MOR34.violation_payload_polynomial
#print axioms MOR34.searchStates_mono
#print axioms MOR34.computedPipeline_polynomial_payload

#print axioms MOR34.rowSearchCalls_polynomial
#print axioms MOR34.counted_ilp_cost_bound
#print axioms MOR34.allNormalCandidateCalls_bound

#print axioms MOR34.external_compression_application

#print axioms MOR34.computedReturnedBasis_rank_calls
#print axioms MOR34.binaryPointMatrix_entry_bits
#print axioms MOR34.binaryMatrixPayload_bound
#print axioms MOR34.binaryBasisSearch_rank_payload_states

#print axioms MOR34.facet_component_bound_parameter
#print axioms MOR34.raw_facet_component_bound

#print axioms MOR34.forcedSystem_polynomial_payload
#print axioms MOR34.violationSystem_polynomial_payload

#print axioms MOR34.six_power_parameter_bound
#print axioms MOR34.normal_calls_parameter_bound
#print axioms MOR34.rowCallFactor_parameter_bound
#print axioms MOR34.normal_calls_original_parameter

#print axioms MOR34.computedReturnedBasis_rank_calls_polynomial
#print axioms MOR34.counted_rank_cost_bound

#print axioms MOR34.minor_arithmetic_bound
#print axioms MOR34.columnNormalCharge_bound
#print axioms MOR34.normalKeyCharge_bound
#print axioms MOR34.matrixNormalArithmeticCharge_bound
#print axioms MOR34.normalBasisArithmeticCharge_bound

#print axioms MOR34.adjacentWitnessTable_length
#print axioms MOR34.edgePointsFromTable_length
#print axioms MOR34.storedEdgePoints_length
#print axioms MOR34.storedEdgePoints_mem
#print axioms MOR34.storedEdgePoints_eq
#print axioms MOR34.storedReturnedSets_eq
#print axioms MOR34.adjacent_exchange_uses_one_solve
#print axioms MOR34.all_solver_calls_bound

#print axioms MOR34.allNormalArithmeticCharge_bound
#print axioms MOR34.normalKeyBudget_factorial_bound
#print axioms MOR34.normalKeyBudget_parameter_bound
#print axioms MOR34.allNormalArithmeticCharge_parameter
#print axioms MOR34.all_solver_cost_bound

#print axioms MOR34.chargedPhaseCost_bound

#print axioms MOR34.normalWorkBits_polynomial
#print axioms MOR34.normalCheck_signed_bits
#print axioms MOR34.determinant_signed_bits
#print axioms MOR34.counted_normal_bit_cost

#print axioms MOR34.sumConstruction_value
#print axioms MOR34.sumConstruction_work
#print axioms MOR34.prefixConstruction_value
#print axioms MOR34.prefixConstruction_work
#print axioms MOR34.atomicIntegerRow_value
#print axioms MOR34.atomicIntegerRow_work
#print axioms MOR34.construction_fold_value
#print axioms MOR34.construction_fold_work
#print axioms MOR34.parityRowConstruction_value
#print axioms MOR34.parityRowConstruction_work

#print axioms MOR34.adjacentPairKey_injective

#print axioms MOR34.prefixRowConstruction_value
#print axioms MOR34.prefixRowConstruction_work
#print axioms MOR34.countRowConstruction_value
#print axioms MOR34.countRowConstruction_work
#print axioms MOR34.countParityConstructionWork_bound
#print axioms MOR34.cellConstructionWork_polynomial

#print axioms MOR34.binarySetKey_coordinate_count
#print axioms MOR34.returnedFamily_pairwise_work
#print axioms MOR34.returnedFamily_coordinate_work

#print axioms MOR34.forcedSlopeConstruction_value
#print axioms MOR34.forcedSlopeConstruction_work
#print axioms MOR34.forcedEmptyConstruction_value
#print axioms MOR34.forcedEmptyConstruction_work
#print axioms MOR34.forcedOrdinaryConstruction_value
#print axioms MOR34.forcedRowConstruction_value
#print axioms MOR34.forcedRowConstruction_work
#print axioms MOR34.forcedConstructionWork_polynomial

#print axioms MOR34.violationRowConstruction_value
#print axioms MOR34.violationRowConstruction_work
#print axioms MOR34.violationConstructionWork_polynomial

#print axioms MOR34.storedNormalizedPipeline_eq
#print axioms MOR34.storedNormalizedPipeline_correct
#print axioms MOR34.storedRawPipeline_eq
#print axioms MOR34.storedRawPipeline_correct

#print axioms MOR34.chargedMap_value

#print axioms MOR34.chargedMap_cost

#print axioms MOR34.chargedFlatMap_value

#print axioms MOR34.chargedFlatMap_cost

#print axioms MOR34.chargedFilter_value

#print axioms MOR34.chargedFilter_cost

#print axioms MOR34.chargedFinFunctions_value

#print axioms MOR34.chargedFinFunctions_cost

#print axioms MOR34.functionEnumerationBudget_bound

#print axioms MOR34.chargedFinFunctions_parameter_cost

#print axioms MOR34.chargedRankKeys_value

#print axioms MOR34.rankKey_length_bound

#print axioms MOR34.chargedRankKeys_cost

#print axioms MOR34.chargedNormalKeys_value

#print axioms MOR34.chargedNormalKeys_cost

#print axioms MOR34.matrixNormalSearchBuilt_value

#print axioms MOR34.matrixNormalSearchBuilt_cost

#print axioms MOR34.residualIndexList_finset

#print axioms MOR34.residualIndexList_sorted

#print axioms MOR34.residualIndexList_length

#print axioms MOR34.chargedResidualWeights_value

#print axioms MOR34.chargedResidualWeights_length

#print axioms MOR34.builtResidualWeight_eq

#print axioms MOR34.chargedResidualWeights_cost

#print axioms MOR34.residual_table_polynomial_work

#print axioms MOR34.chargedFilterMap_value

#print axioms MOR34.chargedFilterMap_cost

#print axioms MOR34.adjacentAt_complete

#print axioms MOR34.chargedClassAdjacencies_length

#print axioms MOR34.chargedClassAdjacencies_cost

#print axioms MOR34.chargedAdjacentIndices_complete

#print axioms MOR34.chargedAdjacentIndices_length

#print axioms MOR34.chargedAdjacentIndices_cost

#print axioms MOR34.chargedAllResidualTables_length

#print axioms MOR34.chargedAllResidualTables_contains

#print axioms MOR34.chargedAllResidualTables_cost

#print axioms MOR34.normalEnumerationCharge_bound

#print axioms MOR34.allNormalEnumerationCharge_bound

#print axioms MOR34.arithmetic_and_enumeration_parameter_bound

#print axioms MOR34.compressed_size_offset_bound

#print axioms MOR34.compression_cost_substitution_two

#print axioms MOR34.compressed_core_and_preprocessing

#print axioms MOR34.constructedWitnessTable_length

#print axioms MOR34.constructedEdgePoints_mem

#print axioms MOR34.constructedEdgePoints_eq_stored

#print axioms MOR34.constructedReturnedSets_eq

#print axioms MOR34.constructedNormalizedPipeline_eq

#print axioms MOR34.constructedNormalizedPipeline_correct

#print axioms MOR34.chargedListRead_value

#print axioms MOR34.chargedListRead_cost

#print axioms MOR34.storedResidualRead_value

#print axioms MOR34.storedResidualRead_cost

#print axioms MOR34.prefixIndexList_sorted

#print axioms MOR34.chargedPrefixConstruction_value

#print axioms MOR34.chargedPrefixConstruction_interpret

#print axioms MOR34.chargedPrefixConstruction_cost

#print axioms MOR34.builtCountForms_value

#print axioms MOR34.builtCountForms_cost

#print axioms MOR34.builtNormalBasisSearch_value

#print axioms MOR34.builtNormalBasisSearch_cost

#print axioms MOR34.builtPrefixRow_value

#print axioms MOR34.builtPrefixRow_cost

#print axioms MOR34.builtForcedSlope_value

#print axioms MOR34.builtForcedSlope_cost

#print axioms MOR34.builtForcedRow_value

#print axioms MOR34.builtForcedRow_cost

#print axioms MOR34.builtForcedRows_interpret

#print axioms MOR34.builtForcedRows_total_cost

#print axioms MOR34.builtCountRow_value

#print axioms MOR34.builtCountRow_interpret

#print axioms MOR34.builtCountRow_cost

#print axioms MOR34.builtCountRows_total_cost

#print axioms MOR34.denseQueryTable_read_bound

#print axioms MOR34.builtViolationRow_value

#print axioms MOR34.builtViolationRow_interpret

#print axioms MOR34.builtViolationRow_cost

#print axioms MOR34.builtViolationRows_total_cost

#print axioms MOR34.normalKeyBuildBudget_parameter_bound

#print axioms MOR34.normalEnumerationFactor_parameter_bound

#print axioms MOR34.builtNormalParameter_bound

#print axioms MOR34.builtForcedRows_common_budget

#print axioms MOR34.allRowConstruction_budget

#print axioms MOR34.constructionPhase_budget

#print axioms MOR34.readPrefixConstruction_value

#print axioms MOR34.readPrefixConstruction_cost

#print axioms MOR34.storedIntegerRead_cost

#print axioms MOR34.storedIntegerRead_of_present

#print axioms MOR34.retainedResidualScalar_value

#print axioms MOR34.retainedResidualPrefix_value

#print axioms MOR34.retainedResidualPrefix_cost

#print axioms MOR34.retainedSlopeRow_value

#print axioms MOR34.retainedSlopeRow_cost

#print axioms MOR34.retainedForcedRow_value

#print axioms MOR34.retainedForcedRow_cost

#print axioms MOR34.retainedForcedRow_interpret

#print axioms MOR34.chargedMap_cost_eq

#print axioms MOR34.evaluateInteger_value

#print axioms MOR34.evaluateInteger_cost

#print axioms MOR34.evaluateConstructedRow_arrays

#print axioms MOR34.evaluateConstructedRow_sized

#print axioms MOR34.evaluateConstructedRow_value

#print axioms MOR34.evaluateConstructedRow_cost

#print axioms MOR34.compileRetainedRow_value

#print axioms MOR34.compileRetainedRow_cost

#print axioms MOR34.forcedRowIndexList_complete

#print axioms MOR34.forcedRowIndexList_length

#print axioms MOR34.retainedForcedSystem_sized

#print axioms MOR34.retainedForcedSystem_iff

#print axioms MOR34.retainedForcedSystem_cost

#print axioms MOR34.compiledForcedRequest_sized

#print axioms MOR34.compiledForcedRequest_iff

#print axioms MOR34.compiledForcedRequest_cost

#print axioms MOR34.denseForcedOracle_spec

#print axioms MOR34.chargedDenseForcedSolve_cost

#print axioms MOR34.denseForced_normalized_correct

#print axioms MOR34.denseParityRow_arrays

#print axioms MOR34.denseParityRow_value

#print axioms MOR34.denseParityRow_sized

#print axioms MOR34.denseParityRow_cost

#print axioms MOR34.compileParityRow_value

#print axioms MOR34.compileParityRow_sized

#print axioms MOR34.compiledCountParity_cost

#print axioms MOR34.countRowIndexList_complete

#print axioms MOR34.countRowIndexList_length

#print axioms MOR34.compiledCountRequest_sized

#print axioms MOR34.compiledCountRequest_iff

#print axioms MOR34.compiledCountRequest_cost

#print axioms MOR34.denseCountOracle_spec

#print axioms MOR34.chargedDenseCountSolve_cost

#print axioms MOR34.violationRowIndexList_complete

#print axioms MOR34.violationRowIndexList_length

#print axioms MOR34.compiledViolationRequest_sized

#print axioms MOR34.compiledViolationRequest_iff

#print axioms MOR34.compiledViolationRequest_cost

#print axioms MOR34.denseViolation_spec

#print axioms MOR34.chargedDenseViolationSolve_cost

#print axioms MOR34.denseNormalizedPipeline_correct

#print axioms MOR34.expression_value_magnitude

#print axioms MOR34.constructionSubterm_work

#print axioms MOR34.constructionSubterm_literals

#print axioms MOR34.constructionSubterm_bits

#print axioms MOR34.constructionSubterm_bits_polynomial

#print axioms MOR34.chargedFirstWitness_value

#print axioms MOR34.chargedFirstWitness_cost

#print axioms MOR34.chargedDescendingSearch_value

#print axioms MOR34.chargedDescendingSearch_cost

#print axioms MOR34.chargedBasisExecution_value

#print axioms MOR34.chargedBasisExecution_cost

#print axioms MOR34.sumConstruction_literals

#print axioms MOR34.prefixConstruction_literals

#print axioms MOR34.integerPick_magnitude

#print axioms MOR34.atomicIntegerRow_literals

#print axioms MOR34.prefixRowConstruction_literals

#print axioms MOR34.countRowConstruction_literals

#print axioms MOR34.countRow_subterm_bits

#print axioms MOR34.chargedOutsideQueries_value

#print axioms MOR34.chargedOutsideQueries_cost

#print axioms MOR34.chargedCellStep_value

#print axioms MOR34.chargedCellStep_cost

#print axioms MOR34.chargedBasisExecution_cost_on_states

#print axioms MOR34.chargedCellBasis_value

#print axioms MOR34.denseRawPipeline_correct

#print axioms MOR34.denseRawPipeline_facet

#print axioms MOR34.dense_original_input_output_contract

#print axioms MOR34.storedList_ofFn

#print axioms MOR34.densePayload_of_value

#print axioms MOR34.completeEnumeration_sum

#print axioms MOR34.denseCompiledList_payload

#print axioms MOR34.compiledForcedRequest_payload

#print axioms MOR34.compiledCountRequest_payload

#print axioms MOR34.compiledViolationRequest_payload

#print axioms MOR34.compiledForcedRequest_payload_polynomial

#print axioms MOR34.compiledViolationRequest_payload_polynomial

#print axioms MOR34.denseProblemSize_polynomial

#print axioms MOR34.compiledForcedRequest_length

#print axioms MOR34.compiledCountRequest_length

#print axioms MOR34.compiledViolationRequest_length

#print axioms MOR34.actualForcedSolver_cost

#print axioms MOR34.actualViolationSolver_cost

#print axioms MOR34.actualCellSolver_cost

#print axioms MOR34.actualCellRequest_cost

#print axioms MOR34.denseCellRequests_cost_on_states

#print axioms MOR34.weightedEvaluateInteger_value

#print axioms MOR34.weightedEvaluateInteger_cost

#print axioms MOR34.weightedEvaluateInteger_cost_of_literals

#print axioms MOR34.boundedCountRequest_payload

#print axioms MOR34.boundedCountSolver_cost

#print axioms MOR34.simpleQuery_normal_bound

#print axioms MOR34.maximumScanQuery_bound

#print axioms MOR34.minimumScanQuery_bound


#print axioms MOR34.searchStates_and

#print axioms MOR34.chargedCellBasis_cost_of_query_states

#print axioms MOR34.chargedParityDecode_value

#print axioms MOR34.chargedParityDecode_cost

#print axioms MOR34.chargedDecodedRequest_value

#print axioms MOR34.chargedDecodedRequest_cost

#print axioms MOR34.parity_solution_count_bounds

#print axioms MOR34.chargedCellBasis_cost_on_contained_states

#print axioms MOR34.chargedDenseCellQuery_value

#print axioms MOR34.chargedDenseCellBasis_value

#print axioms MOR34.chargedDenseCellBasis_cost

#print axioms MOR34.chargedDenseListQuery_value

#print axioms MOR34.chargedDenseListQuery_cost

#print axioms MOR34.chargedCoordinateScan_value

#print axioms MOR34.chargedCoordinateScan_cost

#print axioms MOR34.chargedFinTable_value

#print axioms MOR34.chargedFinTable_cost

#print axioms MOR34.chargedCoordinateWitness_value

#print axioms MOR34.extremaFromTables_eq

#print axioms MOR34.chargedDenseExtrema_value

#print axioms MOR34.chargedDenseExtrema_cost

#print axioms MOR34.chargedModeFamily_value

#print axioms MOR34.chargedModeFamily_cost

#print axioms MOR34.chargedModeFamily_length

#print axioms MOR34.chargedDenseModes_value

#print axioms MOR34.chargedDenseModes_cost

#print axioms MOR34.chargedDenseModes_length

#print axioms MOR34.chargedDenseParityFamily_value

#print axioms MOR34.chargedDenseParityFamily_cost

#print axioms MOR34.chargedDenseParityFamily_length

#print axioms MOR34.chargedDenseSelection_value

#print axioms MOR34.chargedDenseSelection_cost

#print axioms MOR34.chargedCellRestrictions_value

#print axioms MOR34.chargedCellRestrictions_cost

#print axioms MOR34.denseCellQueryBudget_polynomial

#print axioms MOR34.chargedCellStepBudget_scale

#print axioms MOR34.denseCellLoopBudget_polynomial

#print axioms MOR34.denseModesBudget_polynomial

#print axioms MOR34.denseExtremaBudget_polynomial

#print axioms MOR34.denseParityBudget_polynomial

#print axioms MOR34.chargedDenseSelection_polynomial

#print axioms MOR34.chargedDenseSelection_length

#print axioms MOR34.chargedDenseSelection_set

#print axioms MOR34.chargedDenseSelection_points

#print axioms MOR34.chargedDenseSelection_span

#print axioms MOR34.chargedRankOutside_value

#print axioms MOR34.chargedRankOutside_cost

#print axioms MOR34.chargedRankStep_value

#print axioms MOR34.chargedRankStep_cost

#print axioms MOR34.chargedRankBasis_value

#print axioms MOR34.chargedRankBasis_cost

#print axioms MOR34.chargedDenseSupport_nonempty

#print axioms MOR34.forcedSlopeConstruction_literals

#print axioms MOR34.forcedEmptyConstruction_literals

#print axioms MOR34.forcedRowConstruction_literals

#print axioms MOR34.violationRowConstruction_literals

#print axioms MOR34.construction_fold_literals

#print axioms MOR34.parityRowConstruction_literals

#print axioms MOR34.IntegerArithmeticCharge.Bounded.mono

#print axioms MOR34.weightedEvaluateRow_value

#print axioms MOR34.weightedEvaluateRow_cost

#print axioms MOR34.uniformRowRadius_clog

#print axioms MOR34.uniformRowRadius_dominates

#print axioms MOR34.weightedEvaluateRow_polynomial

#print axioms MOR34.weightedCountRow_polynomial
#print axioms MOR34.weightedForcedRow_polynomial
#print axioms MOR34.weightedViolationRow_polynomial
#print axioms MOR34.chargedDenseSupport_value
#print axioms MOR34.chargedDenseSupport_cost
#print axioms MOR34.chargedDenseRecognition_value
#print axioms MOR34.chargedDenseRecognition_cost
#print axioms MOR34.chargedAdjacentWitness_value
#print axioms MOR34.chargedWitnessTable_value
#print axioms MOR34.chargedEdgePoints_value
#print axioms MOR34.chargedEdgePoints_cost
#print axioms MOR34.chargedDenseEdges_value
#print axioms MOR34.chargedDenseEdges_cost
#print axioms MOR34.chargedBinaryRank_value
#print axioms MOR34.chargedBinaryRank_cost
#print axioms MOR34.chargedFinalBasis_value
#print axioms MOR34.chargedFinalBasis_cost
#print axioms MOR34.chargedReturnedFamily_value
#print axioms MOR34.chargedReturnedFamily_length
#print axioms MOR34.chargedReturnedFamily_cost
#print axioms MOR34.chargedNormalizedExecution_value
#print axioms MOR34.chargedNormalizedExecution_correct
#print axioms MOR34.chargedNormalizedExecution_cost

#print axioms MOR34.uniformPolynomial_parameter

#print axioms MOR34.uniformPolynomial_n

#print axioms MOR34.uniformPolynomial_L

#print axioms MOR34.uniformPolynomial_add

#print axioms MOR34.uniformPolynomial_mul

#print axioms MOR34.uniformPolynomial_pow

#print axioms MOR34.normalizedExecutionBudget_uniform

#print axioms MOR34.normalizedExecutionBudget_mono

#print axioms MOR34.normalizedExecutionBudget_fpt

#print axioms MOR34.complete_reference_application

#print axioms MOR34.complete_compressed_reference_application

#print axioms MOR34.chargedRelabelDecision_value

#print axioms MOR34.chargedRelabelDecision_cost

#print axioms MOR34.chargedRelabelOutput_value

#print axioms MOR34.chargedRelabelOutput_cost

#print axioms MOR34.chargedRawExecution_correct

#print axioms MOR34.weightedDenseParityRow_value

#print axioms MOR34.weightedDenseParityRow_polynomial

#print axioms MOR34.weightedCompileParityRow_value

#print axioms MOR34.chargedNormalizedExecution_basis_card

#print axioms MOR34.chargedRawExecution_cost

#print axioms MOR34.pricedParityEntry_value

#print axioms MOR34.sharedWeightedDenseParityRow_value

#print axioms MOR34.sharedWeightedDenseParityRow_cost

#print axioms MOR34.weightedCompileRetainedRow_value

#print axioms MOR34.sharedWeightedCompileParityRow_value

#print axioms MOR34.weightedCompiledCountRequest_value

#print axioms MOR34.weightedCompiledViolationRequest_value

#print axioms MOR34.weightedCompiledForcedRequest_value

#print axioms MOR34.weightedRequests_solver_inputs

#print axioms MOR34.constructedRow_coordinate_work

#print axioms MOR34.evaluatedRow_magnitudes

#print axioms MOR34.expressionMagnitude_clog

#print axioms MOR34.sharedWeightedCompileParityRow_cost

#print axioms MOR34.parityOperandEnvelope_polynomial

#print axioms MOR34.weightedBuiltCountParity_polynomial

#print axioms MOR34.weightedCompiledCountRequest_polynomial

#print axioms MOR34.forms_cell_query_literals

#print axioms MOR34.weightedReachedCellRequests_polynomial
#print axioms MOR34.chargedMap_cost_additive
#print axioms MOR34.weightedRetainedRow_cost_additive
#print axioms MOR34.weightedViolationRequest_cost
#print axioms MOR34.weightedForcedRequest_cost
#print axioms MOR34.weightedRemainingRequests_polynomial
#print axioms MOR34.parameterMajorant_le
#print axioms MOR34.rawReferenceBudget_uniform
#print axioms MOR34.original_reference_application
#print axioms MOR34.prepend_standard_preprocessing
#print axioms MOR34.weightedDenseCountSolve_value
#print axioms MOR34.weightedDenseCellQuery_value
#print axioms MOR34.weightedCellQuery_cost_on_states
#print axioms MOR34.weightedDenseCellBasis_value
#print axioms MOR34.weightedDenseCellBasis_cost
#print axioms MOR34.weightedCellLoopBudget_uniform
#print axioms MOR34.weightedCellLoopBudget_mono
#print axioms MOR34.weightedCellLoopBudget_fpt
#print axioms MOR34.preparedCountForms_value
#print axioms MOR34.preparedCountForms_cost
#print axioms MOR34.orderedCountMatrix_bound
#print axioms MOR34.preparedNormalCheck_bits
#print axioms MOR34.preparedNormalMinor_bits
#print axioms MOR34.preparedCountForms_polynomial
#print axioms MOR34.preparedCellStep_value
#print axioms MOR34.preparedCellStep_cost
#print axioms MOR34.preparedCellBasis_value
#print axioms MOR34.preparedCellBasis_cost_on_states
#print axioms MOR34.preparedCellBudget_uniform
