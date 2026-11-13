module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeCompatibleMaps
public import SerrePositivity.KST.Spectra.RawSpectrumHomPoints
public import SerrePositivity.KST.Spectra.SpectrumPointedEnrichment
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterSquares

/-!
概要：補助単位の相対 BF 左因子と可換な全 Hom の組を合成する。
方針：制限条件を点つき単位パラメータの正方形へ移し、既存の豊穣正方形合成を使う。
規約：選択した持ち上げの通常関手性を使わない。
使われ方：相対 BF 比較を保持する局所 Kan な豊穣圏の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 概要：元の BF 射の単位パラメータでの合成は、同じ射の前合成。
方針：各段で curry' と閉構造の合成の公式を適用する。
規約：全 Hom パラメータ上の厳密等式。
使われ方：相対 BF 左因子の正方形条件への移送。 -/
lemma homPoint_composition_pre {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (Z : KanSequence.{u}) :
    homPoint X Y.toKanSequence ⟨f.app, f.comm⟩ ▷ pointedSpace Y Z ≫
        pointedComposition X Y Z =
      (λ_ (pointedSpace Y Z)).hom ≫ pointedPre f Z := by
  apply pointed_hom_ext X Z
  intro n
  rw [Category.assoc, pointedComposition_evaluation]
  dsimp only [pointedCompositionFamily]
  rw [whiskerRight_comp_tensorHom_assoc, homPoint_evaluation,
    tensorHom_def', Category.assoc]
  change 𝟙_ PointedSimplicialSet.{u} ◁ pointedEvaluation Y Z n ≫
    curry' (f.app n) ▷ ((ihom (Y.level n).space).obj (Z.level n).space) ≫
    comp (X.level n).space (Y.level n).space (Z.level n).space = _
  rw [curry'_whiskerRight_comp (f.app n)]
  erw [leftUnitor_naturality_assoc (pointedEvaluation Y Z n)]
  rw [Category.assoc, pointedPre_evaluation, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]

/-- 概要：元の列射の単位パラメータでの合成は、同じ射の後合成。
方針：各段で curry' の後合成の公式と右単位子の自然性を使う。
規約：元の列射の段を変えない。
使われ方：相対 BF 左因子の正方形条件への移送。 -/
lemma homPoint_composition_post (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (f : Y ⟶ Z) :
    pointedSpace X Y.toKanSequence ◁ homPoint Y Z.toKanSequence ⟨f.app, f.comm⟩ ≫
        pointedComposition X Y Z.toKanSequence =
      (ρ_ (pointedSpace X Y.toKanSequence)).hom ≫
        pointedPost X (⟨f.app, f.comm⟩ : KanSequence.Hom Y.toKanSequence Z.toKanSequence) := by
  apply pointed_hom_ext X Z.toKanSequence
  intro n
  rw [Category.assoc, pointedComposition_evaluation]
  dsimp only [pointedCompositionFamily]
  rw [whiskerLeft_comp_tensorHom_assoc, homPoint_evaluation,
    tensorHom_def, Category.assoc]
  change pointedEvaluation X Y.toKanSequence n ▷ 𝟙_ PointedSimplicialSet.{u} ≫
    ((ihom (X.level n).space).obj (Y.level n).space) ◁ curry' (f.app n) ≫
    comp (X.level n).space (Y.level n).space (Z.level n).space = _
  rw [whiskerLeft_curry'_comp (f.app n)]
  erw [rightUnitor_naturality_assoc (pointedEvaluation X Y.toKanSequence n)]
  rw [Category.assoc, pointedPost_evaluation]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping

namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance : EnrichedCategory PointedSimplicialSet.{u} OmegaSpectrum.{u} :=
  pointedEnrichment

/-- 概要：相対左因子を全 Hom の元の単位パラメータとして保持する。
方針：厳密な BF 左因子を同じ全整合 Hom の点へ移す。
規約：選択した別の辺を使わない。
使われ方：豊穣正方形の共通境界。 -/
def inclusionPoint (X : OmegaSpectrum.{u}) :
    𝟙_ PointedSimplicialSet.{u} ⟶
      RawSpectrumMapping.pointedSpace X (middle X).toKanSequence :=
  RawSpectrumMapping.homPoint X (middle X).toKanSequence
    ⟨(inclusion X).app, (inclusion X).comm⟩

/-- 概要：全 Hom の可換条件を元の単位パラメータ付き豊穣正方形へ移す。
方針：左右の単位子を打ち消し、同じ射の前合成と後合成の式を使う。
規約：任意の点つきパラメータを保つ同値。
使われ方：可換な組の全パラメータでの合成。 -/
lemma compatible_condition_iff (X Y : OmegaSpectrum.{u})
    {P : PointedSimplicialSet.{u}}
    (g : P ⟶ RawSpectrumMapping.pointedSpace (middle X) (middle Y).toKanSequence)
    (f : P ⟶ RawSpectrumMapping.pointedSpace X Y.toKanSequence) :
    g ≫ RawSpectrumMapping.pointedPre (inclusion X) (middle Y).toKanSequence =
        f ≫ inclusionPost X Y ↔
      (inclusionPoint X ⊗ₘ g) ≫
          RawSpectrumMapping.pointedComposition X (middle X) (middle Y).toKanSequence =
        (β_ (𝟙_ PointedSimplicialSet.{u}) P).hom ≫ (f ⊗ₘ inclusionPoint Y) ≫
          RawSpectrumMapping.pointedComposition X Y (middle Y).toKanSequence := by
  rw [tensorHom_def', Category.assoc, inclusionPoint,
    RawSpectrumMapping.homPoint_composition_pre]
  rw [tensorHom_def, Category.assoc, inclusionPoint,
    RawSpectrumMapping.homPoint_composition_post]
  change _ ↔ _ = (β_ (𝟙_ PointedSimplicialSet.{u}) P).hom ≫
    f ▷ 𝟙_ PointedSimplicialSet.{u} ≫
    (ρ_ (RawSpectrumMapping.pointedSpace X Y.toKanSequence)).hom ≫ inclusionPost X Y
  rw [leftUnitor_naturality_assoc, rightUnitor_naturality_assoc]
  simp only [← Category.assoc, braiding_rightUnitor]
  simpa only [Category.assoc] using (cancel_epi (λ_ P).hom).symm

/-- 概要：二つの可換な組を射影ごとに合成しても指定左因子と厳密可換。
方針：同じ単位パラメータの豊穣正方形を合成する。
規約：全 smash パラメータを保持する。
使われ方：実引き戻しへの合成射の構成。 -/
lemma compatible_composition_condition (X Y Z : OmegaSpectrum.{u}) :
    (replacedMap X Y ⊗ₘ replacedMap Y Z) ≫
        RawSpectrumMapping.pointedComposition (middle X) (middle Y) (middle Z).toKanSequence ≫
          RawSpectrumMapping.pointedPre (inclusion X) (middle Z).toKanSequence =
      (originalMap X Y ⊗ₘ originalMap Y Z) ≫
        RawSpectrumMapping.pointedComposition X Y Z.toKanSequence ≫ inclusionPost X Z := by
  rw [← Category.assoc, ← Category.assoc]
  apply (compatible_condition_iff X Z _ _).mpr
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_square_comp PointedSimplicialSet.{u}
    (C := OmegaSpectrum.{u}) (inclusionPoint X) (inclusionPoint Y) (inclusionPoint Z)
    (replacedMap X Y) (originalMap X Y) (replacedMap Y Z) (originalMap Y Z)
    ((compatible_condition_iff X Y _ _).mp (compatible_condition X Y))
    ((compatible_condition_iff Y Z _ _).mp (compatible_condition Y Z))

/-- 概要：指定単位の相対左因子と可換な全 Hom の組の実際の合成。
方針：射影ごとの元の豊穣合成を同じ引き戻しへ持ち上げる。
規約：元の射と置換後の射の両方を保持する。
使われ方：全 Hom 上の自然性を実現する豊穣構造。 -/
def compatibleComposition (X Y Z : OmegaSpectrum.{u}) :
    compatibleSpace X Y ⊗ compatibleSpace Y Z ⟶ compatibleSpace X Z :=
  pullback.lift
    ((replacedMap X Y ⊗ₘ replacedMap Y Z) ≫
      RawSpectrumMapping.pointedComposition (middle X) (middle Y) (middle Z).toKanSequence)
    ((originalMap X Y ⊗ₘ originalMap Y Z) ≫
      RawSpectrumMapping.pointedComposition X Y Z.toKanSequence)
    (compatible_composition_condition X Y Z)

/-- 概要：合成から置換後の射を取り出すと元の豊穣合成となる。
方針：実引き戻しの第一射影式を使う。
規約：全 Hom の射の等式。
使われ方：相対 BF 比較の合成法則。 -/
@[reassoc (attr := simp)]
lemma compatibleComposition_replacedMap (X Y Z : OmegaSpectrum.{u}) :
    compatibleComposition X Y Z ≫ replacedMap X Z =
      (replacedMap X Y ⊗ₘ replacedMap Y Z) ≫
        RawSpectrumMapping.pointedComposition (middle X) (middle Y) (middle Z).toKanSequence :=
  pullback.lift_fst _ _ _

/-- 概要：合成から元の射を取り出すと元の豊穣合成となる。
方針：実引き戻しの第二射影式を使う。
規約：元の BF Hom のまま比較する。
使われ方：相対 BF 比較の合成法則。 -/
@[reassoc (attr := simp)]
lemma compatibleComposition_originalMap (X Y Z : OmegaSpectrum.{u}) :
    compatibleComposition X Y Z ≫ originalMap X Z =
      (originalMap X Y ⊗ₘ originalMap Y Z) ≫
        RawSpectrumMapping.pointedComposition X Y Z.toKanSequence :=
  pullback.lift_snd _ _ _

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
