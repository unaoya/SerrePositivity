module
public import SerrePositivity.InfinityCategories.Derived.PinchedBoundaryFilling
public import SerrePositivity.InfinityCategories.Derived.ContractingElementHomBoundaries
public import SerrePositivity.InfinityCategories.Core.ContractibleKan

/-! # 収縮対象に接する dg nerve の写像空間の可縮性

概要：収縮対象へ入る／出る pinched Hom は可縮な Kan 複体。
方針：Hom の全閉元の原始元から正次元の全境界を充填し、零次元では零射を使う。
規約：可縮性は実際の全境界の充填で示す。使われ方：β3 の商での零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 全閉元の原始元があれば、dg nerve の pinched Hom は可縮な Kan 複体。 -/
lemma pinchedHom_isContractibleKan_of_primitives
    (p : ∀ k : ℤ, GradedHom A x y (k + 1) → GradedHom A x y k)
    (hp : ∀ k a, differential A a = 0 → differential A (p k a) = a) :
    IsContractibleKan (DGNerve.pinchedHom A D x y) := by
  intro n b
  cases n with
  | zero =>
    exact ⟨SSet.yonedaEquiv.symm ((0 : LinearSimplex A x y 0).toPinched),
      SSet.boundary.hom_ext₀⟩
  | succ n => exact pinchedBoundaryFilling b p hp

/-- 終点が収縮するなら、そこへ入る dg nerve の写像空間は可縮。 -/
lemma contractingTargetPinchedHom_isContractibleKan (h : GradedHom A y y (-1))
    (dh : (homObject A D y y).d (-1) 0 h = (unitElement A y).val) :
    IsContractibleKan (DGNerve.pinchedHom A D x y) :=
  pinchedHom_isContractibleKan_of_primitives (contractingTargetPrimitive h)
    (contractingTargetPrimitive_differential h dh)

/-- 始点が収縮するなら、そこから出る dg nerve の写像空間は可縮。 -/
lemma contractingSourcePinchedHom_isContractibleKan (h : GradedHom A x x (-1))
    (dh : (homObject A D x x).d (-1) 0 h = (unitElement A x).val) :
    IsContractibleKan (DGNerve.pinchedHom A D x y) :=
  pinchedHom_isContractibleKan_of_primitives (contractingSourcePrimitive h)
    (contractingSourcePrimitive_differential h dh)

end SerrePositivity.InfinityCategories
