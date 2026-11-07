import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleCartesian

set_option pp.universes true
set_option pp.explicit true

-- reference dfd87a26c159f64b880f
#check @isInvertibleEdge_iff_isCartesianEdge
#print axioms isInvertibleEdge_iff_isCartesianEdge

-- reference ba196331d2f4ffc29ea5
#check @isInvertibleEdge_iff_isCocartesianEdge
#print axioms isInvertibleEdge_iff_isCocartesianEdge

-- reference 77270a4b72bad7029220
#check @isCartesianEdge_of_isInvertibleEdge
#print axioms isCartesianEdge_of_isInvertibleEdge

-- reference 397af2fe6e532fdf1b31
#check @isCocartesianEdge_constant
#print axioms isCocartesianEdge_constant
