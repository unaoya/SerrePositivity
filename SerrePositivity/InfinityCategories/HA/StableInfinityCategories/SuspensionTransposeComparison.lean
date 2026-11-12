module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionTranspose
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareTransposeEvaluation

/-! # 転置と suspension の標準比較

概要：標準比較は転置と両立し、二枝の交換の自己同型は二乗すると恒等になる。
方針：始点成分による比較の一意性と、転置で対角頂点の評価が不変なことを使う。
規約：負の恒等射との一致は未証明。使われ方：TR2 の符号の同定の準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：suspension 図式の標準比較の転置は、転置した二図式の標準比較である。
方針：始点成分の転置不変性を使い、比較の始点成分による一意性を適用する。
規約：安定性は不要。使われ方：suspension 頂点の標準比較の転置不変性。 -/
lemma SuspensionSquare.diagramComparisonIso_hom_transpose {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (hoFunctor.map ((pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).app X)).toFunctor.map
      (s.diagramComparisonIso r).hom = (s.transpose.diagramComparisonIso r.transpose).hom := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparison_hom_ext s.transpose.square s.transpose.isPushout r.transpose
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation_transpose]
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom s.square s.isPushout (r.changeSource s.source_eq.symm)) =
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom s.transpose.square s.transpose.isPushout
        (r.transpose.changeSource s.transpose.source_eq.symm))
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_source, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_source]

/-- 概要：suspension 頂点間の標準比較は、両方の四角形を転置しても同じ射となる。
方針：図式の標準比較の転置との両立を右上の頂点で評価する。
規約：始点・終点は転置前後で同じ。使われ方：交換作用の二乗の計算。 -/
lemma SuspensionSquare.comparisonIso_hom_transpose {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (s.transpose.comparisonIso r.transpose).hom = (s.comparisonIso r).hom := by
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map
      (s.transpose.diagramComparisonIso r.transpose).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map (s.diagramComparisonIso r).hom
  rw [← s.diagramComparisonIso_hom_transpose r]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation_transpose _ _

/-- 概要：二枝の交換の標準比較は、逆向きの標準比較と同じ射である。
方針：二回の転置が元に戻ることを標準比較の転置不変性に代入する。
規約：負の恒等射との一致はまだ含まない。使われ方：交換が involution であること。 -/
lemma SuspensionSquare.swapIso_hom_eq_reverse {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    s.swapIso.hom = (s.transpose.comparisonIso s).hom := by
  have h := congrArg Arrow.mk (s.comparisonIso_hom_transpose s.transpose)
  have ht := congrArg (fun r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x =>
    (Arrow.mk (s.transpose.comparisonIso r).hom : Arrow (hoFunctor.obj X))) s.transpose_transpose
  apply Arrow.mk_injective
  exact h.symm.trans ht

/-- 概要：二枝の交換が suspension 頂点に誘導する射は二回の合成で恒等射になる。
方針：第二の交換を逆向きの標準比較とし、標準比較の合成則を使う。
規約：安定性は不要。使われ方：負の恒等射との比較の整合条件。 -/
lemma SuspensionSquare.swapIso_hom_comp_self {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    s.swapIso.hom ≫ s.swapIso.hom = 𝟙 (SSet.HomotopyCategory.mk s.vertex) := by
  calc
    _ = (s.comparisonIso s.transpose).hom ≫ (s.transpose.comparisonIso s).hom := by
      rw [← s.swapIso_hom_eq_reverse]
      rfl
    _ = (s.comparisonIso s).hom :=
      congrArg Iso.hom (s.comparisonIso_trans s.transpose s)
    _ = _ := by rw [s.comparisonIso_self]; rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
