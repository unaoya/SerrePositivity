module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleFunctorEdgePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorFamilyTranspose

/-!
概要：元の可逆辺の path を、その辺を与えた同じ区間族へ戻す。
方針：Yoneda 表現と二変数交換の逆性を使う。
規約：端点や比較の代表を変更しない。
使われ方：可逆三角形の面と既存の Hom 比較 path を厳密に同定する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 元の族の二度の転置は同じ全高次の族。 -/
lemma transposeFunctorFamily_involutive {A I Y : SSet.{u}} (F : A ⟶ (ihom I).obj Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily F) = F := by
  apply uncurry_injective
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily, uncurry_curry]
  apply SSet.hom_ext
  intro n
  rfl

/-- 同じ可逆辺を与える区間族は、既存の path の包含と厳密に一致する。 -/
lemma invertibleFunctorEdgePath_ι_of_family {A Y : SSet.{u}} [Quasicategory Y]
    {f g : A ⟶ Y}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e)
    (F : A ⟶ (ihom (Δ[1] : SSet.{u})).obj Y)
    (hF : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily F) = e.edge) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.invertibleFunctorEdgePath e he ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y = F := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.invertibleFunctorEdgePath_ι]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (SSet.yonedaEquiv.symm e.edge) = F
  rw [← hF]
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily
    (SSet.yonedaEquiv.symm_apply_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily F))).trans
      (transposeFunctorFamily_involutive F)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
