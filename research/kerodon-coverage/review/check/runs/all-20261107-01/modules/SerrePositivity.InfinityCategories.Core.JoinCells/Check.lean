import SerrePositivity.InfinityCategories.Core.JoinCells

set_option pp.universes true
set_option pp.explicit true

-- reference dd14c7f629f02af2d3b9
#check @leftAnodyneExtensions
#print axioms leftAnodyneExtensions

-- reference 776a995566de5a1a2d0c
#check @leftAnodyneExtensions_horn
#print axioms leftAnodyneExtensions_horn

-- reference cec6490775d8703035fb
#check @rightAnodyneExtensions
#print axioms rightAnodyneExtensions

-- reference 638c2921f4919d9a5f0f
#check @rightAnodyneExtensions_horn
#print axioms rightAnodyneExtensions_horn

-- reference 5e5e29d39861207b6380
#check @joinUnion_rightHorn_boundary_innerAnodyne
#print axioms joinUnion_rightHorn_boundary_innerAnodyne

-- reference 3d4effa07f76b5055bf5
#check @joinUnion_boundary_leftHorn_innerAnodyne
#print axioms joinUnion_boundary_leftHorn_innerAnodyne

-- reference 12f24cad19bb5e89b40e
#check @Join.horn_boundary_preimage
#print axioms Join.horn_boundary_preimage
