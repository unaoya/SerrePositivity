module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionHom

/-! # 全次数 Hom の係数変更比較の両変数自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

@[reassoc]
lemma homComparison_postcompose (K : Complex A) {L L' : Complex A} (g : L ⟶ L') :
    (extension φ).map (homPostcompose K g) ≫ homComparison φ K L' =
      homComparison φ K L ≫ homPostcompose ((extension φ).obj K) ((extension φ).map g) := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro p
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (homComparison φ K L').f p
    ((ModuleCat.extendScalars φ).map ((homPostcompose K g).f p) ((1 : A') ⊗ₜ[A] f)) =
      (homPostcompose ((extension φ).obj K) ((extension φ).map g)).f p
        ((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f))
  erw [ModuleCat.ExtendScalars.map_tmul φ, homPostcompose_apply, homPostcompose_apply]
  apply Cochain.ext
  intro i n h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((homComparison φ K L').f p
    ((1 : A') ⊗ₜ[A] f.comp (Cochain.ofHom g) (add_zero p))).v i n h ((1 : A') ⊗ₜ[A] x) =
      (((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f)).comp
        (Cochain.ofHom ((extension φ).map g)) (add_zero p)).v i n h ((1 : A') ⊗ₜ[A] x)
  erw [homComparison_apply φ K L' p i n h]
  rw [Cochain.comp_zero_cochain_v, Cochain.comp_zero_cochain_v]
  change (1 : A') ⊗ₜ[A] g.f n (f.v i n h x) =
    (ModuleCat.extendScalars φ).map (g.f n)
      (((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f)).v i n h ((1 : A') ⊗ₜ[A] x))
  erw [homComparison_apply φ K L p i n h, ModuleCat.ExtendScalars.map_tmul φ]

@[reassoc]
lemma homComparison_precompose {K K' : Complex A} (f : K' ⟶ K) (L : Complex A) :
    (extension φ).map (homPrecompose f L) ≫ homComparison φ K' L =
      homComparison φ K L ≫ homPrecompose ((extension φ).map f) ((extension φ).obj L) := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro p
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change (homComparison φ K' L).f p
    ((ModuleCat.extendScalars φ).map ((homPrecompose f L).f p) ((1 : A') ⊗ₜ[A] g)) =
      (homPrecompose ((extension φ).map f) ((extension φ).obj L)).f p
        ((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] g))
  erw [ModuleCat.ExtendScalars.map_tmul φ, homPrecompose_apply, homPrecompose_apply]
  apply Cochain.ext
  intro i n h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((homComparison φ K' L).f p
    ((1 : A') ⊗ₜ[A] (Cochain.ofHom f).comp g (zero_add p))).v i n h ((1 : A') ⊗ₜ[A] x) =
      ((Cochain.ofHom ((extension φ).map f)).comp
        ((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] g)) (zero_add p)).v i n h ((1 : A') ⊗ₜ[A] x)
  erw [homComparison_apply φ K' L p i n h]
  rw [Cochain.zero_cochain_comp_v, Cochain.zero_cochain_comp_v]
  change (1 : A') ⊗ₜ[A] g.v i n h (f.f i x) =
    ((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] g)).v i n h
      ((ModuleCat.extendScalars φ).map (f.f i) ((1 : A') ⊗ₜ[A] x))
  erw [ModuleCat.ExtendScalars.map_tmul φ, homComparison_apply φ K L p i n h]

end SerrePositivity.DifferentialGraded.ScalarExtension
