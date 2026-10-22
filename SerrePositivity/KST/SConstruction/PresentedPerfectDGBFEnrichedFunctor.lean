module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFMapping

/-! # 厳密 dg 入力上の実 BF スペクトル値厳密豊穣関手
概要：元の全実段と全 Hom 作用を持つ BF Ω スペクトル値 K を構成する。
方針：写像塔への持ち上げを各段へ評価し、元の豊穣恒等・合成保存を使う。
規約：構造射の可換性は厳密。使われ方：γ1 による Sp 値 ∞ 関手。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ元のスペクトル写像空間による BF の単体的豊穣を使用する。 -/
local instance presentedPerfectDGBFTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 同じ実 BF 全 Hom 作用は元の豊穣単位を保存する。 -/
lemma presentedPerfectDGBFMapping_id (X : PerfDGInput.{u, v} A) :
    eId SSet X ≫ presentedPerfectDGBFMapping A X X =
      eId SSet (presentedPerfectDGBFOmegaSpectrum A X) := by
  apply OmegaSpectrum.mapping_hom_ext
  intro n
  rw [Category.assoc, presentedPerfectDGBFMapping_evaluation]
  exact (presentedPerfectDGBFLevelFunctor A n).map_id X |>.trans
    (OmegaSpectrum.mappingIdentity_evaluation (presentedPerfectDGBFOmegaSpectrum A X) n).symm

/-- 同じ実 BF 全 Hom 作用は元の豊穣合成を保存する。 -/
lemma presentedPerfectDGBFMapping_comp (X Y Z : PerfDGInput.{u, v} A) :
    eComp SSet X Y Z ≫ presentedPerfectDGBFMapping A X Z =
      (presentedPerfectDGBFMapping A X Y ⊗ₘ presentedPerfectDGBFMapping A Y Z) ≫
        eComp SSet (presentedPerfectDGBFOmegaSpectrum A X)
          (presentedPerfectDGBFOmegaSpectrum A Y) (presentedPerfectDGBFOmegaSpectrum A Z) := by
  apply OmegaSpectrum.mapping_hom_ext
  intro n
  rw [Category.assoc, presentedPerfectDGBFMapping_evaluation]
  change _ = (presentedPerfectDGBFMapping A X Y ⊗ₘ presentedPerfectDGBFMapping A Y Z) ≫
    OmegaSpectrum.mappingComposition _ _ _ ≫ OmegaSpectrum.evaluation _ _ n
  rw [OmegaSpectrum.mappingComposition_evaluation]
  change _ = (presentedPerfectDGBFMapping A X Y ⊗ₘ presentedPerfectDGBFMapping A Y Z) ≫
    (OmegaSpectrum.evaluation _ _ n ⊗ₘ OmegaSpectrum.evaluation _ _ n) ≫ _
  erw [← Category.assoc, tensorHom_comp_tensorHom,
    presentedPerfectDGBFMapping_evaluation, presentedPerfectDGBFMapping_evaluation]
  exact (presentedPerfectDGBFLevelFunctor A n).map_comp X Y Z

/-- 全厳密 dg 入力と全高次 Hom を保つ、実 BF Ω スペクトル値厳密豊穣関手。 -/
def presentedPerfectDGBFEnrichedFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      OmegaSpectrum.{max (u + 1) v} where
  obj := presentedPerfectDGBFOmegaSpectrum A
  map := presentedPerfectDGBFMapping A
  map_id := presentedPerfectDGBFMapping_id A
  map_comp := presentedPerfectDGBFMapping_comp A

/-- 同じ厳密豊穣関手の対象は元の実再帰 BF Ω スペクトル。 -/
lemma presentedPerfectDGBFEnrichedFunctor_obj (X : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFEnrichedFunctor A).obj X = presentedPerfectDGBFOmegaSpectrum A X := rfl

/-- 同じ厳密豊穣関手の全 Hom 作用は、各段で元の作用を回収する。 -/
lemma presentedPerfectDGBFEnrichedFunctor_evaluation (X Y : PerfDGInput.{u, v} A) (n : ℕ) :
    (presentedPerfectDGBFEnrichedFunctor A).map X Y ≫
        OmegaSpectrum.evaluation (presentedPerfectDGBFOmegaSpectrum A X)
          (presentedPerfectDGBFOmegaSpectrum A Y) n =
      (presentedPerfectDGBFLevelFunctor A n).map X Y :=
  presentedPerfectDGBFMapping_evaluation A X Y n

end SerrePositivity.KST.SConstruction
