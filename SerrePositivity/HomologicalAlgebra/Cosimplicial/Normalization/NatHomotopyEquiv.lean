module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Normalization.ProjectorKernels

/-!
# 指定した核の包含のDold–Kanホモトピー逆

Dold–Kanの正規化とBerger–Fresse §2.2、M14 L21、報告 §399。
同じ射影を元の全codegeneracy核へ制限し、指定包含との両合成を判定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.CosimplicialNormalization
open _root_.CategoryTheory _root_.HomologicalComplex _root_.AlgebraicTopology
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat.{u} A))

/-- 同じDold–Kan射影を元の核に制限した逆射（Dold–Kan）。 -/
def normalizationRetractionNat :
    (alternatingCofaceMapComplex (ModuleCat A)).obj X ⟶ _root_.SerrePositivity.CosimplicialNormalization.normalizedCochainNat A X :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom
    { toFun a := ⟨(_root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat A X).f q a, _root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat_mem A X q a⟩
      map_add' a b := by apply Subtype.ext; exact map_add _ _ _
      map_smul' r a := by apply Subtype.ext; exact map_smul _ _ _ }) (fun q => by
    dsimp only [_root_.SerrePositivity.CosimplicialNormalization.normalizedCochainNat, alternatingCofaceMapComplex,
      AlternatingCofaceMapComplex.obj]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    have H := ConcreteCategory.congr_hom ((_root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat A X).comm q (q + 1)) a
    dsimp only [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj] at H
    rw [CochainComplex.of_d] at H
    change _root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces A X q ((_root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat A X).f q a) =
      (_root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat A X).f (q + 1) ((AlternatingCofaceMapComplex.objD X q) a)
    rw [_root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces_eq_objD_hom]
    exact H)

/-- 元の指定包含の後の逆射は核上の恒等（Dold–Kan）。 -/
lemma normInclusionNat_retraction :
    _root_.SerrePositivity.CosimplicialNormalization.normInclusionNat A X ≫ _root_.SerrePositivity.CosimplicialNormalization.normalizationRetractionNat A X = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact _root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat_normalized A X q a

/-- 逆射の後の元の指定包含は同じDold–Kan射影（Dold–Kan）。 -/
lemma normalizationRetractionNat_inclusion :
    _root_.SerrePositivity.CosimplicialNormalization.normalizationRetractionNat A X ≫ _root_.SerrePositivity.CosimplicialNormalization.normInclusionNat A X = _root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat A X := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-- 指定した核の包含そのものをhomとするホモトピー同値（Dold–Kan）。 -/
def normalizationHomotopyEquivNat :
    HomotopyEquiv (_root_.SerrePositivity.CosimplicialNormalization.normalizedCochainNat A X)
      ((alternatingCofaceMapComplex (ModuleCat A)).obj X) where
  hom := _root_.SerrePositivity.CosimplicialNormalization.normInclusionNat A X
  inv := _root_.SerrePositivity.CosimplicialNormalization.normalizationRetractionNat A X
  homotopyHomInvId := Homotopy.ofEq (_root_.SerrePositivity.CosimplicialNormalization.normInclusionNat_retraction A X)
  homotopyInvHomId := (Homotopy.ofEq (_root_.SerrePositivity.CosimplicialNormalization.normalizationRetractionNat_inclusion A X)).trans
    (_root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat_homotopy A X)

end SerrePositivity.CosimplicialNormalization
