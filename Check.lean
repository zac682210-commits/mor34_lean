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
