module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconeStrictCycles
public import SerrePositivity.InfinityCategories.Derived.Gluing.BiproductCycles
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaComparison

/-! 任意次数の厳密な二成分から、第三成分零の閉 comma 元を構成する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : DGFunctorCommaObject R C E F) (n : ℤ)
  (a : (homObject R C X.source Y.source).X n)
  (b : (homObject R E X.replacement Y.replacement).X n)
local notation "P" => homObject R C X.source Y.source
local notation "Q" => homObject R E X.replacement Y.replacement
local notation "d" => dgFunctorCommaDifference R C E F X Y

/-- 同じ二つの斉次成分を、第三成分零の comma Hom の元へ持ち上げる。 -/
def dgGluingCommaStrictGradedElement : (dgFunctorCommaHomComplex R C E F X Y).X n :=
  dgGluingCoconeStrictElement d n (dgGluingBiproductElement P Q n a b)

lemma dgGluingCommaStrictGradedElement_source :
    (dgFunctorCommaSourceHomMap R C E F X Y).f n
      (dgGluingCommaStrictGradedElement R C E F X Y n a b) = a := by
  change (biprod.fst : P ⊞ Q ⟶ P).f n
    ((mappingCocone.fst d).f n
      (dgGluingCoconeStrictElement d n (dgGluingBiproductElement P Q n a b))) = a
  rw [dgGluingCoconeStrictElement_fst, dgGluingBiproductElement_fst]

lemma dgGluingCommaStrictGradedElement_replacement :
    (dgFunctorCommaReplacementHomMap R C E F X Y).f n
      (dgGluingCommaStrictGradedElement R C E F X Y n a b) = b := by
  change (biprod.snd : P ⊞ Q ⟶ Q).f n
    ((mappingCocone.fst d).f n
      (dgGluingCoconeStrictElement d n (dgGluingBiproductElement P Q n a b))) = b
  rw [dgGluingCoconeStrictElement_fst, dgGluingBiproductElement_snd]

lemma dgGluingCommaStrictGradedElement_primitive :
    (dgFunctorCommaPrimitive R C E F X Y).v n (n - 1) (by omega)
      (dgGluingCommaStrictGradedElement R C E F X Y n a b) = 0 :=
  dgGluingCoconeStrictElement_snd d n (dgGluingBiproductElement P Q n a b)

/-- 閉じた二成分の厳密正方形は、同じ任意次数の閉 comma 元を与える。 -/
lemma dgGluingCommaStrictGradedElement_closed
    (ha : (homObject R C X.source Y.source).d n (n + 1) a = 0)
    (hb : (homObject R E X.replacement Y.replacement).d n (n + 1) b = 0)
    (hd : (d).f n (dgGluingBiproductElement P Q n a b) = 0) :
    (dgFunctorCommaHomComplex R C E F X Y).d n (n + 1)
      (dgGluingCommaStrictGradedElement R C E F X Y n a b) = 0 :=
  dgGluingCoconeStrictElement_closed d n (dgGluingBiproductElement P Q n a b)
    (dgGluingBiproductElement_closed P Q n a b ha hb) hd

end SerrePositivity.InfinityCategories
