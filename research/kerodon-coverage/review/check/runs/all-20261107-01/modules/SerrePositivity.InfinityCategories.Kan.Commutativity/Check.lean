import SerrePositivity.InfinityCategories.Kan.Commutativity

set_option pp.universes true
set_option pp.explicit true

-- reference 3394b4fac832417b3bf3
#check @KanHomotopyGroup.mul_comm
#print axioms KanHomotopyGroup.mul_comm

-- reference e94864047502a76f68bc
#check @instCommGroupKanHomotopyGroupHAddNatOfNat
#print axioms instCommGroupKanHomotopyGroupHAddNatOfNat

-- reference ff4a41c4a718338ce5cd
#check @FourStruct
#print axioms FourStruct

-- reference 7d1bc3eedfc456ab762c
#check @FourStruct.exists_fill
#print axioms FourStruct.exists_fill

-- reference 156af41532aa8b60598f
#check @SimplexFaces.degenerate_face
#print axioms SimplexFaces.degenerate_face

-- reference 8ea82e205d941154ffad
#check @FourReduction.mulStruct
#print axioms FourReduction.mulStruct

-- reference 651aaa5352fe9aa93934
#check @FourReduction.class_eq
#print axioms FourReduction.class_eq

-- reference 09652f6deaa2a2e0839e
#check @AdjacentProduct.flip
#print axioms AdjacentProduct.flip
