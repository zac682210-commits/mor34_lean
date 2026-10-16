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
