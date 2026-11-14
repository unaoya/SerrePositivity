module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.OppositeInternalHom
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeInternalHomTrivialFibration
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：元の相対関手制限の標的を反転後の相対内部 Hom の標的と同型にする。
方針：反転が保つ引き戻しの三つの頂点を内部 Hom の反転同型で移す。
規約：相対制限と二つの射影との可換性を射の等式で保持する。
使われ方：元の相対右 Kan 制限へ左の制限定理を移す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：相対内部 Hom の標的の反転は反転後の相対制限の引き戻しを表す。
方針：引き戻しを反転し、内部 Hom の三つの標準同型で移す。
規約：図式と標的に充填性は不要。
使われ方：相対標的の反転同型の普遍性。 -/
lemma kanRelativeInternalHom_op_isPullback {K C D E : SSet.{u}}
    (δ : K ⟶ C) (U : D ⟶ E) (s : internalHom.PullbackObjObj δ U) :
    IsPullback
      (SSet.opFunctor.map s.fst ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso K D).hom)
      (SSet.opFunctor.map s.snd ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso C E).hom)
      ((ihom K.op).map (SSet.opFunctor.map U)) ((pre (SSet.opFunctor.map δ)).app E.op) := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  exact (s.isPullback.map SSet.opFunctor).of_iso (Iso.refl _)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso K D) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso C E)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso K E)
    (by simp only [Iso.refl_hom, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.id_comp])
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHom_post K U) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHom_pre δ E)

/-- 概要：元の相対標的の反転は反転後の相対標的と厳密に同型。
方針：同じ引き戻しの二つの表現の一意な同型を使う。
規約：両側の相対内部 Hom の引き戻しの選択を明示する。
使われ方：元と標的の図式を同時に保つ右制限の双対移送。 -/
def kanRelativeInternalHomOppositeIso {K C D E : SSet.{u}}
    (δ : K ⟶ C) (U : D ⟶ E) (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj (SSet.opFunctor.map δ) (SSet.opFunctor.map U)) :
    s.pt.op ≅ t.pt := (kanRelativeInternalHom_op_isPullback δ U s).isoIsPullback _ _ t.isPullback

/-- 概要：相対標的の反転同型の第一成分は元の図式の反転。
方針：引き戻しの比較同型の第一射影の式。
規約：全単体での厳密な可換性。
使われ方：元の制限図式の保存。 -/
lemma kanRelativeInternalHomOppositeIso_hom_fst {K C D E : SSet.{u}}
    (δ : K ⟶ C) (U : D ⟶ E) (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj (SSet.opFunctor.map δ) (SSet.opFunctor.map U)) :
    (kanRelativeInternalHomOppositeIso δ U s t).hom ≫ t.fst =
      SSet.opFunctor.map s.fst ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso K D).hom := by
  exact IsPullback.isoIsPullback_hom_fst _ _
    (kanRelativeInternalHom_op_isPullback δ U s) t.isPullback

/-- 概要：相対標的の反転同型の第二成分は標的の図式の反転。
方針：引き戻しの比較同型の第二射影の式。
規約：全単体での厳密な可換性。
使われ方：元の U 像の図式の保存。 -/
lemma kanRelativeInternalHomOppositeIso_hom_snd {K C D E : SSet.{u}}
    (δ : K ⟶ C) (U : D ⟶ E) (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj (SSet.opFunctor.map δ) (SSet.opFunctor.map U)) :
    (kanRelativeInternalHomOppositeIso δ U s t).hom ≫ t.snd =
      SSet.opFunctor.map s.snd ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso C E).hom := by
  exact IsPullback.isoIsPullback_hom_snd _ _
    (kanRelativeInternalHom_op_isPullback δ U s) t.isPullback

/-- 概要：元の相対内部 Hom の比較の反転は反転後の比較と同型の下で可換。
方針：二つの射影へ合成し、前合成と後合成の反転自然性を使う。
規約：相対制限の指定された射自体を比較する。
使われ方：元の右 Kan 制限の写像空間と左側の制限との対応。 -/
lemma kanRelativeInternalHomOppositeIso_comparison {K C D E : SSet.{u}}
    (δ : K ⟶ C) (U : D ⟶ E) (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj (SSet.opFunctor.map δ) (SSet.opFunctor.map U)) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso C D).hom ≫ t.π =
      SSet.opFunctor.map s.π ≫ (kanRelativeInternalHomOppositeIso δ U s t).hom := by
  apply t.hom_ext
  · rw [Category.assoc, t.π_fst, Category.assoc, kanRelativeInternalHomOppositeIso_hom_fst,
      ← Category.assoc, ← Functor.map_comp, s.π_fst]
    exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHom_pre δ D).symm
  · rw [Category.assoc, t.π_snd, Category.assoc, kanRelativeInternalHomOppositeIso_hom_snd,
      ← Category.assoc, ← Functor.map_comp, s.π_snd]
    exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHom_post C U).symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
