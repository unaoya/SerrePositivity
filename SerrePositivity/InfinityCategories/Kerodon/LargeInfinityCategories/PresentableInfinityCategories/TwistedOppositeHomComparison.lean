module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowTarget
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ClassificationTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityConstruction

/-!
概要：反対圏の全 twisted Hom 族と元の両端を交換した Hom 族の比較。
方針：公開された twisted arrow の両端交換同型を同じ底変換として分類する。
規約：全二変数の自然同型を構成し、対象対ごとの同値で代用しない。
使われ方：全 co-Yoneda 族の充満忠実性と表現可能な Hom 極限の存在判定。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：反対 Hom の共同底を元の共同底へ両端交換で戻す同型。
方針：左右の射影を交換し二重反転を戻す。
規約：元の底の宇宙を保つ。
使われ方：twisted arrow の両端交換を底上の同型として読む。 -/
def oppositeHomBaseIso (C : SSet.{u}) : C.op.op ⊗ C.op ≅ C.op ⊗ C where
  hom := lift (snd _ _) (fst _ _ ≫ (SSet.opFunctorCompOpFunctorIso.app C).hom)
  inv := lift (snd _ _ ≫ (SSet.opFunctorCompOpFunctorIso.app C).inv) (fst _ _)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [Category.assoc]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [Category.assoc]

/-- 概要：元の twisted arrow の両端交換は指定底交換を保つ。
方針：公開された二つの端点公式を合成する。
規約：全写像の厳密な等式である。
使われ方：同じ底変換への比較写像の構成。 -/
lemma twistedArrowOppositeSwap_projection (C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C.op ≫ (oppositeHomBaseIso C).hom := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_fst, oppositeHomBaseIso, lift_fst,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap_left]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_snd C.op).symm
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_snd, oppositeHomBaseIso, lift_snd,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap_right]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_fst]

/-- 概要：反対 twisted arrow から元の指定底変換への比較。
方針：両端交換と元の射影を pullback に束ねる。
規約：同じ小さい全空間を保持する。
使われ方：全分類図式の比較。 -/
def oppositeHomPullbackComparison (C : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C.op ⟶
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (oppositeHomBaseIso C).hom :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C.op)
    (twistedArrowOppositeSwap_projection C)

/-- 概要：同じ底変換への比較は厳密な同型。
方針：底交換の同型性と元の全空間の同型性を用いる。
規約：同値性の仮定を追加しない。
使われ方：分類図式の全自然同型への移送。 -/
instance oppositeHomPullbackComparison_isIso (C : SSet.{u}) :
    IsIso (oppositeHomPullbackComparison C) := by
  let f := pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (oppositeHomBaseIso C).hom
  have : IsIso f := inferInstance
  have hi : IsIso (oppositeHomPullbackComparison C ≫ f) := by
    change IsIso (pullback.lift _ _ _ ≫ pullback.fst _ _)
    rw [pullback.lift_fst]
    infer_instance
  have he : oppositeHomPullbackComparison C =
      (oppositeHomPullbackComparison C ≫ f) ≫ (asIso f).inv := by simp [Category.assoc]
  rw [he]
  infer_instance

/-- 概要：反対 Hom の全共同図式は元の両端交換した全図式と自然同型。
方針：同じ指定底変換を分類し、全空間の同型の分類と合成する。
規約：元の Hom 族全体を保持する。
使われ方：co-Yoneda と反対圏 Yoneda の全自然比較。 -/
def twistedOppositeHomInfinityIso (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map (oppositeHomBaseIso C).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C.op) := by
  have : Quasicategory (C.op.op ⊗ C.op) := quasicategory_of_innerFibration (fst _ _)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)
      (oppositeHomBaseIso C).hom ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.leftClassification_overIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C.op)
      (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (oppositeHomBaseIso C).hom)
      (asIso (oppositeHomPullbackComparison C)) (pullback.lift_snd _ _ _)).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
