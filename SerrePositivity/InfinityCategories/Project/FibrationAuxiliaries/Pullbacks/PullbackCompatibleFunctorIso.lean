module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEdgeRepresentative
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.PullbackCompatibleEdgeHomotopy

/-!
概要：共有頂点への指定像が一致する成分同型を、同じ pullback 上の関手同型へ束ねる。
方針：左の代表辺の像を右の元の代表辺へ両端固定で揃え、円柱を貼り合わせる。
規約：パラメーターは任意。pullback の Kan 性を仮定せず、元の二射と成分同型の類を保持する。
使われ方：元の分類 Hom 作用と補正 pullback 比較の同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks

/-- 元の pullback への同じ射の二射影は、底への合成で一致する。 -/
lemma pullbackProjectionComposite_eq {A X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (a : A ⟶ pullback f g) :
    (a ≫ pullback.fst f g) ≫ f = (a ≫ pullback.snd f g) ≫ g :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun m ↦ a ≫ m) (pullback.condition (f := f) (g := g))).trans
      (Category.assoc _ _ _).symm)

/-- 概要：指定像が一致する成分同型を、元の二射を結ぶ pullback の同型へ束ねる。
方針：整合する辺を貼り合わせ、右成分の可逆性を左ファイブレーションで反映する。
規約：pullback の Kan 性は要求しない。使われ方：指定変換下の族の比較。 -/
def pullbackFunctorIsoOfCompatibleIsos {A X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration f]
    (a b : A ⟶ pullback f g)
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ pullback.fst f g) (b ≫ pullback.fst f g))
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ pullback.snd f g) (b ≫ pullback.snd f g))
    (h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (L.postcomp f)
      (pullbackProjectionComposite_eq f g a) (pullbackProjectionComposite_eq f g b) =
      R.postcomp g) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b := Classical.choice (by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd f g) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd f g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := f))⟩
  have : Quasicategory (pullback f g) := quasicategory_of_innerFibration (pullback.snd f g)
  let r := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge R).map ((truncation 2).map ((ihom A).map g))
  have hr : SSet.Truncated.HomotopyCategory.homMk r = (R.postcomp g).hom := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_homMk R]
    rfl
  obtain ⟨l, hl, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_exists_edge_representative_over f L (R.postcomp g)
    (pullbackProjectionComposite_eq f g a) (pullbackProjectionComposite_eq f g b) h r hr
  let H := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackHomotopyOfCompatibleEdges f g a b l (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge R) hl
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H
  have hm : e.map ((truncation 2).map ((ihom A).map (pullback.snd f g))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge R := by
    apply SSet.Truncated.Edge.ext
    change ((ihom A).map (pullback.snd f g)).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (curry H.h)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge R).edge
    rw [← SSet.yonedaEquiv_comp, ← curry_natural_right]
    dsimp only [H, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackHomotopyOfCompatibleEdges]
    rw [pullback.lift_snd]
    change SSet.yonedaEquiv (curry (uncurry
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge R).edge))) = _
    rw [curry_uncurry, Equiv.apply_symm_apply]
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge
    ((ihom A).map (pullback.snd f g)) e (by rw [hm]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible R)
  exact ⟨asIso (SSet.Truncated.HomotopyCategory.homMk e)⟩)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks
