module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFMapping

/-! # 同じ native 四頂点像上の実 BF スペクトル値厳密豊穣関手
概要：同じ有限入力の全実段と全 Hom 作用を持つ BF Ω スペクトル値 K を構成する。
方針：写像塔への持ち上げを各段へ評価し、元の豊穣恒等・合成保存を使う。
規約：構造射の可換性は厳密。使われ方：γ1 による Sp 値 ∞ 関手。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories DifferentialGraded NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ元のスペクトル写像空間による BF の単体的豊穣を使用する。 -/
local instance nativeFiniteBFTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 同じ実 BF 全 Hom 作用は元の豊穣単位を保存する。 -/
lemma dgKappaNativeBFMapping_id (X : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    eId SSet X ≫ dgKappaNativeBFMapping.{u, v} R D I X X =
      eId SSet (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X) := by
  apply OmegaSpectrum.mapping_hom_ext
  intro n
  rw [Category.assoc, dgKappaNativeBFMapping_evaluation]
  exact (dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).map_id X |>.trans
    (OmegaSpectrum.mappingIdentity_evaluation
      (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X) n).symm

/-- 同じ実 BF 全 Hom 作用は元の豊穣合成を保存する。 -/
lemma dgKappaNativeBFMapping_comp (X Y Z : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    eComp SSet X Y Z ≫ dgKappaNativeBFMapping.{u, v} R D I X Z =
      (dgKappaNativeBFMapping.{u, v} R D I X Y ⊗ₘ dgKappaNativeBFMapping.{u, v} R D I Y Z) ≫
        eComp SSet (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X)
          (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I Y)
          (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I Z) := by
  apply OmegaSpectrum.mapping_hom_ext
  intro n
  rw [Category.assoc, dgKappaNativeBFMapping_evaluation]
  change _ = (dgKappaNativeBFMapping.{u, v} R D I X Y ⊗ₘ dgKappaNativeBFMapping.{u, v} R D I Y Z) ≫
    OmegaSpectrum.mappingComposition _ _ _ ≫ OmegaSpectrum.evaluation _ _ n
  rw [OmegaSpectrum.mappingComposition_evaluation]
  change _ = (dgKappaNativeBFMapping.{u, v} R D I X Y ⊗ₘ dgKappaNativeBFMapping.{u, v} R D I Y Z) ≫
    (OmegaSpectrum.evaluation _ _ n ⊗ₘ OmegaSpectrum.evaluation _ _ n) ≫ _
  erw [← Category.assoc, tensorHom_comp_tensorHom,
    dgKappaNativeBFMapping_evaluation, dgKappaNativeBFMapping_evaluation]
  exact (dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).map_comp X Y Z

/-- 同じ未完備 native 四頂点像と全高次 Hom を保つ、実 BF Ω スペクトル値厳密豊穣関手。 -/
def dgKappaNativeBFEnrichedFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
      OmegaSpectrum.{max (u + 1) v} where
  obj := dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I
  map := dgKappaNativeBFMapping.{u, v} R D I
  map_id := dgKappaNativeBFMapping_id.{u, v} R D I
  map_comp := dgKappaNativeBFMapping_comp.{u, v} R D I

/-- 同じ厳密豊穣関手の対象は元の実再帰 BF Ω スペクトル。 -/
lemma dgKappaNativeBFEnrichedFunctor_obj (X : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFEnrichedFunctor.{u, v} R D I).obj X =
      dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X := rfl

/-- 同じ厳密豊穣関手の全 Hom 作用は、各段で元の作用を回収する。 -/
lemma dgKappaNativeBFEnrichedFunctor_evaluation (X Y : DGKappaNativeBFFiniteInput.{u, v} R D I)
    (n : ℕ) :
    (dgKappaNativeBFEnrichedFunctor.{u, v} R D I).map X Y ≫
        OmegaSpectrum.evaluation (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X)
          (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I Y) n =
      (dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).map X Y :=
  dgKappaNativeBFMapping_evaluation.{u, v} R D I X Y n

end SerrePositivity.KST.SConstruction
