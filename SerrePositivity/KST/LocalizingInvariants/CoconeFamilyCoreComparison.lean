module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.CoconeFamilyCoreComparison

public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyTranspose
public import SerrePositivity.KST.LocalizingInvariants.CorePreimageComparisonPrism
public import SerrePositivity.KST.LocalizingInvariants.FixedSpanApexDenominators

/-!
概要：転置された全族比較の同じ一次単体を、元のパラメータ族の core 比較へ戻す。
方針：内部 Hom 交換の実単体写像で比較辺を戻し、同じ prism の全辺反転を証明する。
規約：全関手同型の代表辺を選び直さず、指定された元の比較辺を使う。
使われ方：有限分母余錐族の比較を元の strict core 逆像の商射へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 同じ比較辺の可逆性から、元の全族の全パラメータ辺の反転を反映する。 -/
lemma spanFunctorEdgeUnflip_invertsAllEdges {K L X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ (ihom L).obj X}
    (l : Truncated.Edge
      (X := (truncation 2).obj ((ihom L).obj ((ihom K).obj X)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K L X F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K L X G)))
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom L).obj ((ihom K).obj X)) l)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges G Set.univ) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F Set.univ := by
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanFunctorEdgeUnflip_isInvertible l hl
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G := asIso
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanFunctorEdgeUnflip l).toTruncated)
  exact (invertsEdges_functorIso_iff e Set.univ).mpr hG

/-- 元の指定比較辺を転置した同じ prism を、商図式の core 内へ厳密に戻す。 -/
def spanFunctorEdgeUnflipCoreHomotopy {K L X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ (ihom L).obj X}
    (l : Truncated.Edge
      (X := (truncation 2).obj ((ihom L).obj ((ihom K).obj X)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K L X F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K L X G)))
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom L).obj ((ihom K).obj X)) l)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges G Set.univ) :
    SSet.Homotopy (allEdgesCoreLift F (spanFunctorEdgeUnflip_invertsAllEdges l hl hG))
      (allEdgesCoreLift G hG) :=
  allEdgesCoreComparisonHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanFunctorEdgeUnflip l).toTruncated
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanFunctorEdgeUnflip_isInvertible l hl)
    (spanFunctorEdgeUnflip_invertsAllEdges l hl hG) hG

lemma spanFunctorEdgeUnflipCoreHomotopy_ι {K L X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ (ihom L).obj X}
    (l : Truncated.Edge
      (X := (truncation 2).obj ((ihom L).obj ((ihom K).obj X)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K L X F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K L X G)))
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom L).obj ((ihom K).obj X)) l)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges G Set.univ) :
    (spanFunctorEdgeUnflipCoreHomotopy l hl hG).h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom L).obj X)).ι =
      uncurry (SSet.yonedaEquiv.symm l.edge ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso L K X).hom) := by
  rw [spanFunctorEdgeUnflipCoreHomotopy, allEdgesCoreComparisonHomotopy_ι]
  change uncurry (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanFunctorEdgeUnflip l).edge) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanFunctorEdgeUnflip_edge, ← SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.KST.LocalizingInvariants
