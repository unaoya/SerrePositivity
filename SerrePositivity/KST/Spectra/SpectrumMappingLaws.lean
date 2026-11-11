module

public import SerrePositivity.KST.Spectra.SpectrumMappingComposition

/-!
概要：Ω スペクトルの写像空間の単位と厳密な圏の法則。
方針：全段への評価で等式を検査し、各段の単体的圏の法則を適用する。
規約：写像空間は切断の逆極限として構成済み。
使われ方：BF 1978 §2、HTT A.3.3。coherent nerve の入力。
-/

@[expose] public section

universe u

open CategoryTheory SSet MonoidalCategory

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 概要：写像空間への射は段ごとの評価で決まる。
方針：切断の極限の一意性を特殊化する。
規約：任意の単体集合を始域に取る。
使われ方：BF 1978 §2。単体的圏の法則の検査。 -/
theorem mapping_hom_ext {X Y : OmegaSpectrum.{u}} {B : SSet.{u}}
    {f g : B ⟶ mappingSpace X Y}
    (h : ∀ n, f ≫ evaluation X Y n = g ≫ evaluation X Y n) : f = g :=
  TruncatedMapping.total_hom_ext _ _ _ _ _ h

/-- 概要：写像空間の単体的単位。
方針：恒等スペクトル射を表す終対象からの射を用いる。
規約：零次単体だけでなく全単体次数で自然な射。
使われ方：BF 1978 §2、HTT A.3.3。Sp の単体的圏の単位。 -/
def mappingIdentity (X : OmegaSpectrum.{u}) : 𝟙_ SSet.{u} ⟶ mappingSpace X X :=
  vertexOfHomMap (𝟙 X)

/-- 概要：写像空間の単位は各段でその段の単体的単位に評価される。
方針：極限の持ち上げを評価し、通常の恒等射の頂点表示を用いる。
規約：任意の段 n。
使われ方：BF 1978 §2。単位律の段ごとの計算。 -/
@[reassoc (attr := simp)]
theorem mappingIdentity_evaluation (X : OmegaSpectrum.{u}) (n : ℕ) :
    mappingIdentity X ≫ evaluation X X n = eId SSet (X.level n).space := by
  have h := TruncatedMapping.familyLift_evaluation
    (fun n ↦ (X.level n).space) (fun n ↦ (X.level n).space)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) X.sigma (mappingStep X X)
    (homFamily (𝟙 X)) (homFamily_condition (𝟙 X)) n
  change mappingIdentity X ≫ evaluation X X n = homFamily (𝟙 X) n at h
  rw [h]
  apply (SSet.unitHomEquiv _).injective
  rw [homFamily, Equiv.apply_symm_apply]
  rw [← PointedEnrichment.vertexEquiv_eq]
  exact congrArg (SSet.unitHomEquiv _) (eHomEquiv_id SSet (X.level n).space)

/-- 概要：写像空間の合成は左単位律を満たす。
方針：各段へ評価して単体的 Hom の左単位律を使う。
規約：単体集合の射の厳密な等式。
使われ方：BF 1978 §2、HTT A.3.3。単体的圏の構成。 -/
theorem mappingIdentity_comp (X Y : OmegaSpectrum.{u}) :
    (λ_ (mappingSpace X Y)).inv ≫ mappingIdentity X ▷ mappingSpace X Y ≫
      mappingComposition X X Y = 𝟙 _ := by
  apply mapping_hom_ext
  intro n
  simp only [Category.assoc, mappingComposition_evaluation, compositionFamily, Category.id_comp]
  rw [whiskerRight_comp_tensorHom_assoc, mappingIdentity_evaluation,
    leftUnitor_inv_comp_tensorHom_assoc]
  exact (congrArg (fun k ↦ evaluation X Y n ≫ k)
    (e_id_comp SSet (X.level n).space (Y.level n).space)).trans (Category.comp_id _)

/-- 概要：写像空間の合成は右単位律を満たす。
方針：各段へ評価して単体的 Hom の右単位律を使う。
規約：単体集合の射の厳密な等式。
使われ方：BF 1978 §2、HTT A.3.3。単体的圏の構成。 -/
theorem mappingComposition_identity (X Y : OmegaSpectrum.{u}) :
    (ρ_ (mappingSpace X Y)).inv ≫ mappingSpace X Y ◁ mappingIdentity Y ≫
      mappingComposition X Y Y = 𝟙 _ := by
  apply mapping_hom_ext
  intro n
  simp only [Category.assoc, mappingComposition_evaluation, compositionFamily, Category.id_comp]
  rw [whiskerLeft_comp_tensorHom_assoc, mappingIdentity_evaluation,
    rightUnitor_inv_comp_tensorHom_assoc]
  exact (congrArg (fun k ↦ evaluation X Y n ≫ k)
    (e_comp_id SSet (X.level n).space (Y.level n).space)).trans (Category.comp_id _)

/-- 概要：スペクトルの写像空間の単体的合成は結合律を満たす。
方針：各段へ評価してテンソルの自然性とその段の豊穣結合律を用いる。
規約：モノイダル結合子を含む厳密な射の等式。
使われ方：BF 1978 §2、HTT A.3.3。coherent nerve の入力の単体的圏。 -/
theorem mappingComposition_assoc (W X Y Z : OmegaSpectrum.{u}) :
    (α_ (mappingSpace W X) (mappingSpace X Y) (mappingSpace Y Z)).inv ≫
      mappingComposition W X Y ▷ mappingSpace Y Z ≫ mappingComposition W Y Z =
    mappingSpace W X ◁ mappingComposition X Y Z ≫ mappingComposition W X Z := by
  apply mapping_hom_ext
  intro n
  simp only [Category.assoc, mappingComposition_evaluation, compositionFamily]
  rw [whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
    mappingComposition_evaluation, mappingComposition_evaluation]
  simp only [compositionFamily]
  rw [← tensorHom_comp_whiskerRight, ← tensorHom_comp_whiskerLeft,
    Category.assoc, ← associator_inv_naturality_assoc]
  simp only [Category.assoc]
  exact congrArg (fun k ↦
    (evaluation W X n ⊗ₘ (evaluation X Y n ⊗ₘ evaluation Y Z n)) ≫ k)
      (e_assoc SSet (W.level n).space (X.level n).space (Y.level n).space (Z.level n).space)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
