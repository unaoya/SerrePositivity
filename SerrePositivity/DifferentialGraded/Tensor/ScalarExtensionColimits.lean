module
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.HomologicalAlgebra.TensorBaseChangeNaturality
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # 非有界複体の係数変更と余極限

任意の環準同型に対する underived な比較。係数環の平坦性は要求しない。
擬同型の保存はこのファイルの余極限保存からは結論しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- 各次数で A' ⊗_A − を施す。 -/
abbrev extension : Complex A ⥤ Complex A' :=
  (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)

/-- 微分を変えずに各次数で係数を制限する。 -/
abbrev restriction : Complex A' ⥤ Complex A :=
  (ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)

/-- 加群の随伴を非有界複体に持ち上げる。 -/
def adjunction : extension φ ⊣ restriction φ :=
  Adjunction.mkOfUnitCounit {
    unit := (ModuleCat.extendRestrictScalarsAdj φ).unit.mapHomologicalComplex (.up ℤ)
    counit := (ModuleCat.extendRestrictScalarsAdj φ).counit.mapHomologicalComplex (.up ℤ)
    left_triangle := by
      apply NatTrans.ext
      funext K
      apply HomologicalComplex.hom_ext
      intro n
      simp
    right_triangle := by
      apply NatTrans.ext
      funext K
      apply HomologicalComplex.hom_ext
      intro n
      simp }

instance : (extension φ).IsLeftAdjoint := (adjunction φ).isLeftAdjoint
instance : (restriction φ).IsRightAdjoint := (adjunction φ).isRightAdjoint

/-- 直和の比較は同じ添字集合を使う。 -/
def coproductIso {I : Type v} [Small.{u} I] (K : I → Complex A) :
    (extension φ).obj (∐ K) ≅ ∐ (fun i => (extension φ).obj (K i)) :=
  PreservesCoproduct.iso (extension φ) K

@[reassoc (attr := simp)]
lemma map_ι_coproductIso {I : Type v} [Small.{u} I] (K : I → Complex A) (i : I) :
    (extension φ).map (Sigma.ι K i) ≫ (coproductIso φ K).hom =
      Sigma.ι (fun i => (extension φ).obj (K i)) i := by
  apply (cancel_mono (coproductIso φ K).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (ι_comp_sigmaComparison (extension φ) K i).symm

/-- coequalizer も平坦性なしで係数拡大と可換する。 -/
def coequalizerIso {K L : Complex A} (f g : K ⟶ L) :
    (extension φ).obj (coequalizer f g) ≅
      coequalizer ((extension φ).map f) ((extension φ).map g) :=
  (PreservesCoequalizer.iso (extension φ) f g).symm

@[reassoc (attr := simp)]
lemma map_π_coequalizerIso {K L : Complex A} (f g : K ⟶ L) :
    (extension φ).map (coequalizer.π f g) ≫ (coequalizerIso φ f g).hom =
      coequalizer.π ((extension φ).map f) ((extension φ).map g) :=
  map_π_preserves_coequalizer_inv (extension φ) f g

/-- 二つの非有界複体の total tensor との比較。 -/
abbrev tensorIso (K L : Complex A) :
    (extension φ).obj (K ⊗ L) ≅ (extension φ).obj K ⊗ (extension φ).obj L :=
  cochainTensorBaseChangeIso φ K L

@[reassoc]
lemma tensorIso_naturality {K K' L L' : Complex A} (f : K ⟶ K') (g : L ⟶ L') :
    (extension φ).map (f ⊗ₘ g) ≫ (tensorIso φ K' L').hom =
      (tensorIso φ K L).hom ≫ ((extension φ).map f ⊗ₘ (extension φ).map g) :=
  cochainTensorBaseChangeIso_naturality φ f g

/-- 恒等係数変更との比較。 -/
def identityIso : extension (RingHom.id A) ≅ 𝟭 (Complex A) :=
  NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId A) (.up ℤ)

/-- 連続した二回の係数変更との比較。 -/
def compositionIso {A'' : Type u} [CommRing A''] (ψ : A' →+* A'') :
    extension φ ⋙ extension ψ ≅ extension (ψ.comp φ) :=
  Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp φ ψ).symm (.up ℤ)

end SerrePositivity.DifferentialGraded.ScalarExtension
