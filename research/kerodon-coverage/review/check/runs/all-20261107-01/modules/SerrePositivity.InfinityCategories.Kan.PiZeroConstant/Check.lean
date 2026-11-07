import SerrePositivity.InfinityCategories.Kan.PiZeroConstant

set_option pp.universes true
set_option pp.explicit true

-- reference ec87591f42bac071d815
#check @PiZeroConstant.discrete
#print axioms PiZeroConstant.discrete

-- reference 244324dc18343dce50d5
#check @PiZeroConstant.homEquiv
#print axioms PiZeroConstant.homEquiv

-- reference c94870e73aa2cb4be56e
#check @PiZeroConstant.component
#print axioms PiZeroConstant.component

-- reference 9e22172e3840feedadcf
#check @PiZeroConstant.fromComponents
#print axioms PiZeroConstant.fromComponents

-- reference 219c298d92b42efed863
#check @discrete_kan
#print axioms discrete_kan
