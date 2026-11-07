import Mathlib.CategoryTheory.Limits.Sifted

set_option pp.universes true
set_option pp.explicit true

-- reference a81a50278d1a15ff086b
#check @CategoryTheory.IsSifted
#print axioms CategoryTheory.IsSifted

-- reference 0804418d82dc9523466c
#check @IsSifted.of_final_functor_from_sifted
#print axioms IsSifted.of_final_functor_from_sifted

-- reference 07568cd65e78b40991fb
#check @isSifted_of_equiv
#print axioms isSifted_of_equiv

-- reference 4a3299501bb5e7666257
#check @isSifted_of_hasBinaryCoproducts_and_nonempty
#print axioms isSifted_of_hasBinaryCoproducts_and_nonempty

-- reference 7b5d0b8ddd8a3df4c273
#check @colim_preservesFiniteProducts_of_isSifted
#print axioms colim_preservesFiniteProducts_of_isSifted

-- reference 5b1ae8d2e7ebe212686d
#check @IsSifted.of_colim_preservesFiniteProducts
#print axioms IsSifted.of_colim_preservesFiniteProducts
