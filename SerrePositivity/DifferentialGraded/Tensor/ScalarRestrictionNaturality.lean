module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionHom

/-! # 全次数 Hom の係数制限比較の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

@[reassoc]
lemma restrictionHom_postcompose (K : Complex A') {L L' : Complex A'} (g : L ⟶ L') :
    (restriction φ).map (homPostcompose K g) ≫ restrictionHom φ K L' =
      restrictionHom φ K L ≫ homPostcompose ((restriction φ).obj K) ((restriction φ).map g) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (f.comp (Cochain.ofHom g) (add_zero p)).map (ModuleCat.restrictScalars φ) =
    (f.map (ModuleCat.restrictScalars φ)).comp
      (Cochain.ofHom ((restriction φ).map g)) (add_zero p)
  rw [Cochain.map_comp, Cochain.map_ofHom]

@[reassoc]
lemma restrictionHom_precompose {K K' : Complex A'} (f : K' ⟶ K) (L : Complex A') :
    (restriction φ).map (homPrecompose f L) ≫ restrictionHom φ K' L =
      restrictionHom φ K L ≫ homPrecompose ((restriction φ).map f) ((restriction φ).obj L) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change ((Cochain.ofHom f).comp g (zero_add p)).map (ModuleCat.restrictScalars φ) =
    (Cochain.ofHom ((restriction φ).map f)).comp
      (g.map (ModuleCat.restrictScalars φ)) (zero_add p)
  rw [Cochain.map_comp, Cochain.map_ofHom]

end SerrePositivity.DifferentialGraded.ScalarExtension
