module
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionExact
public import SerrePositivity.DifferentialGraded.Derived.Ring
public import SerrePositivity.DifferentialGraded.Tensor.KFlatComparison
public import SerrePositivity.DifferentialGraded.Tensor.ObjectwiseKFlat
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeComplex

/-! # 非 flat な係数変更と K-flat 複体

擬同型の両端が A 上 K-flat なら、係数環の flatness は不要。
dg 加群の相対 K-flat 性と評価ごとの A-K-flat 性は区別する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

omit φ in
lemma ringModule_relativeKFlat {K : Complex A} (hK : complexKFlat A K) :
    moduleRelativeKFlat A PUnit.{1} (ringModule A K) := by
  intro L hL
  exact cochainAcyclic_of_iso (hK (L.obj PUnit.unit) (hL PUnit.unit))
    (BalancedTensor.ringIso A (ringModule A K) L).symm

omit φ in
/-- 両端 K-flat な擬同型は、任意の複体との tensor で擬同型。 -/
lemma tensor_quasiIso_of_kFlat_ends {K L : Complex A}
    (hK : complexKFlat A K) (hL : complexKFlat A L) (f : K ⟶ L) [QuasiIso f]
    (T : Complex A) : QuasiIso (cochainTensorMap f (𝟙 T)) := by
  let M := ForgetEnrichment.of (Complex A) (ringModule A K)
  let N := ForgetEnrichment.of (Complex A) (ringModule A L)
  let E := moduleEvaluation A PUnit.{1} PUnit.unit
  let g : M ⟶ N := E.preimage f
  have hg : E.map g = f := E.map_preimage (X := M) (Y := N) f
  have hq : moduleQuasiIso A PUnit.{1} g :=
    (ringModuleQuasiIso_iff A g).2 (by rw [hg]; infer_instance)
  have ht := BalancedTensor.rightTensor_relativeKFlat_quasiIso A PUnit.{1}
    (ringLeftModule A T) (ringModule_relativeKFlat hK) (ringModule_relativeKFlat hL) g hq
  let V := ForgetEnrichment.of (Complex A) (ringLeftModule A T)
  have hn := BalancedTensor.ringIso_naturality A g (𝟙 V)
  simp only [CategoryTheory.Functor.map_id] at hn
  change BalancedTensor.map A PUnit.{1} g (𝟙 V) ≫ _ = _ ≫ (E.map g ⊗ₘ 𝟙 T) at hn
  rw [hg] at hn
  have : QuasiIso (BalancedTensor.map A PUnit.{1} g (𝟙 V)) := ht
  have hc : QuasiIso ((BalancedTensor.ringIso A (ringModule A K) (ringLeftModule A T)).hom ≫
      cochainTensorMap f (𝟙 T)) := by
    change QuasiIso ((BalancedTensor.ringIso A (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) V)).hom ≫ (f ⊗ₘ 𝟙 T))
    rw [← hn]
    infer_instance
  exact quasiIso_of_comp_left (BalancedTensor.ringIso A (ringModule A K) (ringLeftModule A T)).hom _

/-- K-flat な両端の擬同型に対する非 flat 係数拡大の保存。 -/
lemma extension_quasiIso_of_kFlat_ends {K L : Complex A}
    (hK : complexKFlat A K) (hL : complexKFlat A L) (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((extension φ).map f) := by
  let T := cochainSingleZero (baseChangeScalarModule φ)
  have ht := tensor_quasiIso_of_kFlat_ends hK hL f T
  have hswap := cochainTensorSymmetry_naturality (𝟙 T) f
  have hc : QuasiIso (cochainTensorMap (𝟙 T) f ≫ (cochainTensorSymmetry T L).hom) := by
    rw [hswap]
    infer_instance
  have : QuasiIso (cochainTensorMap (𝟙 T) f) :=
    quasiIso_of_comp_right _ (cochainTensorSymmetry T L).hom
  have hn := restrictedBaseChangeComplexIso_naturality φ f
  have hc : QuasiIso ((restriction φ).map ((extension φ).map f) ≫
      (restrictedBaseChangeComplexIso φ L).hom) := by
    rw [hn]
    infer_instance
  have : QuasiIso ((restriction φ).map ((extension φ).map f)) :=
    quasiIso_of_comp_right _ (restrictedBaseChangeComplexIso φ L).hom
  exact (quasiIso_map_iff_of_preservesHomology ((extension φ).map f)
    (ModuleCat.restrictScalars φ)).1 this

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 相対 K-flat 性だけでなく各評価の A-K-flat 性を要求する。 -/
lemma moduleExtension_quasiIso_of_objectwiseKFlat {M N : ModuleCategory A D}
    (hM : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hN : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) N))
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A' (DGBaseChange φ D) ((moduleExtension φ D).map f) := by
  intro x
  rw [moduleExtension_eval]
  have := hf x
  exact extension_quasiIso_of_kFlat_ends φ (hM x) (hN x) _

lemma derivedExtensionComparison_isIso_of_objectwiseKFlat {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M)
    (hP : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) P.obj))
    (hM : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    IsIso (derivedExtensionComparison φ D P) :=
  derivedExtensionComparison_isIso φ D P
    (moduleExtension_quasiIso_of_objectwiseKFlat φ D hP hM P.π P.quasiIso)

end SerrePositivity.DifferentialGraded.ScalarExtension
