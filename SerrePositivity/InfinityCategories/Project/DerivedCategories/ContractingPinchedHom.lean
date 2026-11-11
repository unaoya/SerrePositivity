module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedBoundaryFilling
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ContractingElementHomBoundaries
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan

/-! # 収縮対象に接する dg nerve の写像空間の可縮性

概要：収縮対象へ入る／出る pinched Hom は可縮な Kan 複体。
方針：Hom の全閉元の原始元から正次元の全境界を充填し、零次元では零射を使う。
規約：可縮性は実際の全境界の充填で示す。使われ方：β3 の商での零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 全閉元の原始元があれば、dg nerve の pinched Hom は可縮な Kan 複体。 -/
lemma pinchedHom_isContractibleKan_of_primitives
    (p : ∀ k : ℤ, _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (k + 1) → _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k)
    (hp : ∀ k a, _root_.SerrePositivity.DifferentialGraded.differential A a = 0 → _root_.SerrePositivity.DifferentialGraded.differential A (p k a) = a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) := by
  intro n b
  cases n with
  | zero =>
    exact ⟨SSet.yonedaEquiv.symm ((0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0).toPinched),
      SSet.boundary.hom_ext₀⟩
  | succ n => exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryFilling b p hp

/-- 終点が収縮するなら、そこへ入る dg nerve の写像空間は可縮。 -/
lemma contractingTargetPinchedHom_isContractibleKan (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A y y (-1))
    (dh : (_root_.SerrePositivity.DifferentialGraded.homObject A D y y).d (-1) 0 h = (_root_.SerrePositivity.DifferentialGraded.unitElement A y).val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) :=
  pinchedHom_isContractibleKan_of_primitives (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.contractingTargetPrimitive h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.contractingTargetPrimitive_differential h dh)

/-- 始点が収縮するなら、そこから出る dg nerve の写像空間は可縮。 -/
lemma contractingSourcePinchedHom_isContractibleKan (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A x x (-1))
    (dh : (_root_.SerrePositivity.DifferentialGraded.homObject A D x x).d (-1) 0 h = (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) :=
  pinchedHom_isContractibleKan_of_primitives (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.contractingSourcePrimitive h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.contractingSourcePrimitive_differential h dh)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
