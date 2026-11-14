module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionTransposeComparison

/-! # Suspension の交換作用の自然性

概要：二枝の交換作用は suspension 図式の任意の射と可換である。
方針：二つの合成を始点で照合し、図式の比較の一意性を使って終点で評価する。
規約：安定性や加法性は不要。使われ方：交換作用を負の恒等射と比較する準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：元の suspension と転置の標準比較の始点成分は恒等射。
方針：標準比較の始点成分の等号輸送を計算する。
規約：suspension の指定始点の等号は両方で同じ。使われ方：交換作用の自然性。 -/
lemma SuspensionSquare.diagramComparisonIso_transpose_source {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map (s.diagramComparisonIso s.transpose).hom =
      𝟙 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex s.square 0 0) := by
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom s.square s.isPushout
      (s.transpose.changeSource s.source_eq.symm)) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_source]
  rfl

/-- 概要：二枝を交換する標準図式比較は任意の suspension 図式の射に関して自然。
方針：始点成分を恒等射とし、転置の評価不変性で二つの合成を照合する。
規約：元と先の suspension の始点は異なってよい。使われ方：頂点上の交換作用の自然性。 -/
lemma SuspensionSquare.diagramComparisonIso_transpose_naturality {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare y)
    (a : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r.square)) :
    a ≫ (r.diagramComparisonIso r.transpose).hom =
      (s.diagramComparisonIso s.transpose).hom ≫
        (hoFunctor.map ((pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).app X)).toFunctor.map a := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparison_hom_ext s.square s.isPushout r.transpose
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map _
  rw [Functor.map_comp, Functor.map_comp, s.diagramComparisonIso_transpose_source,
    r.diagramComparisonIso_transpose_source, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation_transpose]
  exact (Category.comp_id (obj := hoFunctor.obj X)
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map a)).trans
      (Category.id_comp (obj := hoFunctor.obj X)
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map a)).symm

/-- 概要：suspension 頂点の二枝交換は任意の suspension 図式の射の終点成分と可換。
方針：図式での交換作用の自然性を右上の頂点で評価する。
規約：追加の安定性・加法性は不要。使われ方：Σ 上の標準交換作用の自然性。 -/
lemma SuspensionSquare.swapIso_naturality {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare y)
    (a : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r.square)) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map a ≫ r.swapIso.hom =
      s.swapIso.hom ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map a := by
  have h := congrArg (fun f => (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map f)
    (s.diagramComparisonIso_transpose_naturality r a)
  rw [Functor.map_comp, Functor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation_transpose] at h
  exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
