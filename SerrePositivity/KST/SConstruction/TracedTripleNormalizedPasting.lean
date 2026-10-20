module
public import SerrePositivity.KST.SConstruction.TracedTripleInterchangePasting
public import SerrePositivity.KST.SConstruction.CorrectionNormalizationPasting
public import SerrePositivity.KST.SConstruction.TracedTripleBinaryGlue

/-! # 元の全六面と両全正規化円柱を保つ同じ三入力比較
概要：元の六面比較へ元の両全正規化円柱を共有全境界ごと貼り、外側二面の全補正辺を回収する。
方針：元の円柱の全入口・全側面固定を同じ相対円柱の二つの pushout に渡す。
規約：全六面・両全円柱・出口の共有全境界を保持し、比較を選び直さない。
使われ方：外側二入力の両全二部分面・両全段面を同じ補正辺路へ貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の左全正規化円柱を全入力境界ごと六面比較へ貼った実写像。 -/
def monicKTracedTripleLeftNormalizationPasting (n : ℕ) :
    correctionNormalizationLeftDomain.{u} ⟶
      (PointedObject.basedHom ((kOmegaSpectrum (F.obj w)).level n).space
        ((kKanSequence (F.obj z)).level n).space).right :=
  fixedCylinderAttachmentMap (SSet.boundary 1).ι correctionNormalizationLeftEdge
    (monicKTracedTripleInterchangePasting F f g h n)
    (monicKTracedTripleFirstPairBinaryGlue F f g h n)
    (by
      simpa only [correctionNormalizationLeftEdge, Category.assoc] using
        congrArg (stdSimplex.δ (2 : Fin 3) ≫ ·)
          (monicKTracedTripleInterchangePasting_first_stage F f g h n))
    (monicKTracedTripleFirstPairBinaryGlue_relative F f g h n)

/-- 中間複体も元の六面比較全体を厳密に保持する。 -/
lemma monicKTracedTripleLeftNormalizationPasting_original (n : ℕ) :
    fixedCylinderAttachmentOriginal (SSet.boundary 1).ι correctionNormalizationLeftEdge ≫
        monicKTracedTripleLeftNormalizationPasting F f g h n =
      monicKTracedTripleInterchangePasting F f g h n :=
  fixedCylinderAttachmentMap_original _ _ _ _ _ _

/-- 元の左全正規化円柱そのものを厳密に回収する。 -/
lemma monicKTracedTripleLeftNormalizationPasting_cell (n : ℕ) :
    fixedCylinderAttachmentCell (SSet.boundary 1).ι correctionNormalizationLeftEdge ≫
        monicKTracedTripleLeftNormalizationPasting F f g h n =
      (monicKTracedTripleFirstPairBinaryGlue F f g h n).h :=
  fixedCylinderAttachmentMap_cell _ _ _ _ _ _

/-- 左出口は、元の左外側二部分三角形の同じ全第一辺。 -/
lemma monicKTracedTripleLeftNormalizationPasting_target (n : ℕ) :
    fixedCylinderAttachmentTarget (SSet.boundary 1).ι correctionNormalizationLeftEdge ≫
        monicKTracedTripleLeftNormalizationPasting F f g h n =
      stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F (f ≫ g) h n).simplex :=
  fixedCylinderAttachmentMap_target _ _ _ _ _ _

/-- 元の全六面と両全正規化円柱を、同じ全入力境界で保持する実写像。 -/
def monicKTracedTripleNormalizedPasting (n : ℕ) :
    correctionNormalizationPasting.{u} ⟶
      (PointedObject.basedHom ((kOmegaSpectrum (F.obj w)).level n).space
        ((kKanSequence (F.obj z)).level n).space).right :=
  fixedCylinderAttachmentMap (SSet.boundary 1).ι correctionNormalizationRightAttachingEdge
    (monicKTracedTripleLeftNormalizationPasting F f g h n)
    (monicKTracedTripleLastPairBinaryGlue F f g h n)
    (by
      rw [correctionNormalizationRightAttachingEdge, Category.assoc,
        monicKTracedTripleLeftNormalizationPasting_original]
      simpa only [correctionNormalizationRightEdge, Category.assoc] using
        congrArg (stdSimplex.δ (2 : Fin 3) ≫ ·)
          (monicKTracedTripleInterchangePasting_last_stage F f g h n))
    (monicKTracedTripleLastPairBinaryGlue_relative F f g h n)

/-- 左円柱までの中間比較全体も、元の同じ実写像。 -/
lemma monicKTracedTripleNormalizedPasting_intermediate (n : ℕ) :
    fixedCylinderAttachmentOriginal (SSet.boundary 1).ι correctionNormalizationRightAttachingEdge ≫
        monicKTracedTripleNormalizedPasting F f g h n =
      monicKTracedTripleLeftNormalizationPasting F f g h n :=
  fixedCylinderAttachmentMap_original _ _ _ _ _ _

/-- 元の全六面を持つ比較複体全体を厳密に回収する。 -/
lemma monicKTracedTripleNormalizedPasting_original (n : ℕ) :
    correctionNormalizationPastingOriginal ≫ monicKTracedTripleNormalizedPasting F f g h n =
      monicKTracedTripleInterchangePasting F f g h n := by
  rw [correctionNormalizationPastingOriginal, Category.assoc,
    monicKTracedTripleNormalizedPasting_intermediate,
    monicKTracedTripleLeftNormalizationPasting_original]

/-- 元の左全正規化円柱そのものを、最終比較複体でも厳密に保持する。 -/
lemma monicKTracedTripleNormalizedPasting_left_cell (n : ℕ) :
    correctionNormalizationPastingLeftCell ≫ monicKTracedTripleNormalizedPasting F f g h n =
      (monicKTracedTripleFirstPairBinaryGlue F f g h n).h := by
  rw [correctionNormalizationPastingLeftCell, Category.assoc,
    monicKTracedTripleNormalizedPasting_intermediate,
    monicKTracedTripleLeftNormalizationPasting_cell]

/-- 元の右全正規化円柱そのものも厳密に保持する。 -/
lemma monicKTracedTripleNormalizedPasting_right_cell (n : ℕ) :
    correctionNormalizationPastingRightCell ≫ monicKTracedTripleNormalizedPasting F f g h n =
      (monicKTracedTripleLastPairBinaryGlue F f g h n).h :=
  fixedCylinderAttachmentMap_cell _ _ _ _ _ _

/-- 左出口は、同じ端点を保つ元の左外側二部分面の同じ全第一辺。 -/
lemma monicKTracedTripleNormalizedPasting_left_target (n : ℕ) :
    correctionNormalizationPastingLeftTarget ≫ monicKTracedTripleNormalizedPasting F f g h n =
      stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F (f ≫ g) h n).simplex := by
  rw [correctionNormalizationPastingLeftTarget, Category.assoc,
    monicKTracedTripleNormalizedPasting_intermediate,
    monicKTracedTripleLeftNormalizationPasting_target]

/-- 右出口も、同じ端点を保つ元の右外側二部分面の同じ全第二辺。 -/
lemma monicKTracedTripleNormalizedPasting_right_target (n : ℕ) :
    correctionNormalizationPastingRightTarget ≫ monicKTracedTripleNormalizedPasting F f g h n =
      stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F f (g ≫ h) n).simplex :=
  fixedCylinderAttachmentMap_target _ _ _ _ _ _

end SerrePositivity.KST.SConstruction
