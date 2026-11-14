module

public import SerrePositivity.EInfinity.CosimplicialNormalization.ProjectorKernels

/-!
# 指定した核の包含のDold–Kanホモトピー逆

Dold–Kanの正規化とBerger–Fresse §2.2、M14 L21、報告 §399。
同じ射影を元の全codegeneracy核へ制限し、指定包含との両合成を判定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.CosimplicialNormalization
open CategoryTheory HomologicalComplex AlgebraicTopology
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat.{u} A))

/-- 同じDold–Kan射影を元の核に制限した逆射（Dold–Kan）。 -/
def normalizationRetractionNat :
    (alternatingCofaceMapComplex (ModuleCat A)).obj X ⟶ normalizedCochainNat A X :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom
    { toFun a := ⟨(cofaceProjectorNat A X).f q a, cofaceProjectorNat_mem A X q a⟩
      map_add' a b := by apply Subtype.ext; exact map_add _ _ _
      map_smul' r a := by apply Subtype.ext; exact map_smul _ _ _ }) (fun q => by
    dsimp only [normalizedCochainNat, alternatingCofaceMapComplex,
      AlternatingCofaceMapComplex.obj]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    have H := ConcreteCategory.congr_hom ((cofaceProjectorNat A X).comm q (q + 1)) a
    dsimp only [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj] at H
    rw [CochainComplex.of_d] at H
    change alternatingCofaces A X q ((cofaceProjectorNat A X).f q a) =
      (cofaceProjectorNat A X).f (q + 1) ((AlternatingCofaceMapComplex.objD X q) a)
    rw [alternatingCofaces_eq_objD_hom]
    exact H)

/-- 元の指定包含の後の逆射は核上の恒等（Dold–Kan）。 -/
lemma normInclusionNat_retraction :
    normInclusionNat A X ≫ normalizationRetractionNat A X = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact cofaceProjectorNat_normalized A X q a

/-- 逆射の後の元の指定包含は同じDold–Kan射影（Dold–Kan）。 -/
lemma normalizationRetractionNat_inclusion :
    normalizationRetractionNat A X ≫ normInclusionNat A X = cofaceProjectorNat A X := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-- 指定した核の包含そのものをhomとするホモトピー同値（Dold–Kan）。 -/
def normalizationHomotopyEquivNat :
    HomotopyEquiv (normalizedCochainNat A X)
      ((alternatingCofaceMapComplex (ModuleCat A)).obj X) where
  hom := normInclusionNat A X
  inv := normalizationRetractionNat A X
  homotopyHomInvId := Homotopy.ofEq (normInclusionNat_retraction A X)
  homotopyInvHomId := (Homotopy.ofEq (normalizationRetractionNat_inclusion A X)).trans
    (cofaceProjectorNat_homotopy A X)

end SerrePositivity.EInfinity.CosimplicialNormalization
