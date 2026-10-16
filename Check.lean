import MOR34

-- Expected future output contains no `sorryAx` or project-specific axioms.
-- This audit file has NOT run successfully in the current environment.
#print axioms MOR34.one_feasible_of_pair_sum
#print axioms MOR34.balanced_values_are_tight
#print axioms MOR34.interior_cut_arithmetic

-- These are propositions, not proved results:
#check MOR34.BalancedSplitGoal
#check MOR34.PairingAtCutGoal
#check MOR34.InteriorExchangeGoal

-- Additional OPEN interfaces; #check is not a proof.
#check MOR34.PaperInterface.PrefixMinimality
#check MOR34.PaperInterface.IntervalExchange
#check MOR34.PaperInterface.ParityInterior
