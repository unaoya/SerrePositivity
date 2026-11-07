import SerrePositivity.KST.Comparison.ExInfinity

set_option pp.universes true
set_option pp.explicit true

-- reference f395dbea3bc969d0c7c9
#check @exInfinity
#print axioms exInfinity

-- reference 0151ef0dccf6e514188a
#check @exInfinityUnit
#print axioms exInfinityUnit

-- reference c609e99edc61a2b1d2e4
#check @exInfinity_preservesFiniteLimits
#print axioms exInfinity_preservesFiniteLimits
