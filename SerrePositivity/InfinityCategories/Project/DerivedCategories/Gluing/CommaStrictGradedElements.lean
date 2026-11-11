module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoconeStrictCycles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.BiproductCycles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaComparison

/-! 任意次数の厳密な二成分から、第三成分零の閉 comma 元を構成する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (n : ℤ)
  (a : (homObject R C X.source Y.source).X n)
  (b : (homObject R E X.replacement Y.replacement).X n)
local notation "P" => homObject R C X.source Y.source
local notation "Q" => homObject R E X.replacement Y.replacement
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y

/-- 同じ二つの斉次成分を、第三成分零の comma Hom の元へ持ち上げる。 -/
def dgGluingCommaStrictGradedElement : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y).X n :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeStrictElement d n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBiproductElement P Q n a b)

lemma dgGluingCommaStrictGradedElement_source :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y).f n
      (dgGluingCommaStrictGradedElement R C E F X Y n a b) = a := by
  change (biprod.fst : P ⊞ Q ⟶ P).f n
    ((mappingCocone.fst d).f n
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeStrictElement d n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBiproductElement P Q n a b))) = a
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeStrictElement_fst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBiproductElement_fst]

lemma dgGluingCommaStrictGradedElement_replacement :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y).f n
      (dgGluingCommaStrictGradedElement R C E F X Y n a b) = b := by
  change (biprod.snd : P ⊞ Q ⟶ Q).f n
    ((mappingCocone.fst d).f n
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeStrictElement d n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBiproductElement P Q n a b))) = b
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeStrictElement_fst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBiproductElement_snd]

lemma dgGluingCommaStrictGradedElement_primitive :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).v n (n - 1) (by omega)
      (dgGluingCommaStrictGradedElement R C E F X Y n a b) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeStrictElement_snd d n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBiproductElement P Q n a b)

/-- 閉じた二成分の厳密正方形は、同じ任意次数の閉 comma 元を与える。 -/
lemma dgGluingCommaStrictGradedElement_closed
    (ha : (homObject R C X.source Y.source).d n (n + 1) a = 0)
    (hb : (homObject R E X.replacement Y.replacement).d n (n + 1) b = 0)
    (hd : (d).f n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBiproductElement P Q n a b) = 0) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y).d n (n + 1)
      (dgGluingCommaStrictGradedElement R C E F X Y n a b) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeStrictElement_closed d n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBiproductElement P Q n a b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBiproductElement_closed P Q n a b ha hb) hd

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
