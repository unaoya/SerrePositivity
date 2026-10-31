module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Milnor
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Maps
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Localization
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import SerrePositivity.HomologicalAlgebra.ModuleTensorCochainExact
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.HomologicalAlgebra.ModelTensorHomologySurjective
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReconstruction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleTower

/-! # 冪ねじれの塔と冪の余核による再構成

## 概要

スカラー a の冪によるねじれの塔と項ごとのねじれ複体を作り、その holim が非輪状であることを示す。冪の掛け算の像と余核の塔を作り、完備で平坦な複体を通常の冪の余核の holim から再構成する（自然性つき）。平坦なモデルでは冪の余核が商係数のテンソルを計算し、Koszul の塔から通常の冪の商の塔への augmentation を与える。逆極限の有界な冪ねじれの判定も与える。

## 方針

再構成は、ねじれ・像・余核の三つの塔の短完全列を holim へ移し、ねじれの holim が非輪状であることを使う。

## 規約

PowerTorsionTensor などの Tor 側は HA3 の Tor へ移すのが自然（refactor-plan §3.5.1）なので別のまま。

## 使われ方

導来完備化の平坦な場合の比較、BS の完全忠実平坦な降下。
-/

@[expose] public noncomputable section

universe u v

section PowerTorsionTowerPart

namespace SerrePositivity.DerivedCompletion
variable {R : Type u} [CommRing R] (a : R) (M : Type v)
    [AddCommGroup M] [Module R M]

/-- The actual kernel of multiplication by the n-th power. -/
abbrev powerTorsionModule (n : ℕ) : Submodule R M :=
  (a ^ n • (LinearMap.id : M →ₗ[R] M)).ker

/-- The error tower transition is multiplication by a, not the inclusion. -/
def powerTorsionTransition (n : ℕ) :
    powerTorsionModule a M (n + 1) →ₗ[R] powerTorsionModule a M n where
  toFun x := ⟨a • (x : M), by
    change a ^ n • (a • (x : M)) = 0
    have hx : a ^ (n + 1) • (x : M) = 0 := x.property
    simpa only [smul_smul, ← pow_succ] using hx⟩
  map_add' x y := by apply Subtype.ext; exact smul_add a (x : M) (y : M)
  map_smul' r x := by
    apply Subtype.ext
    change a • (r • (x : M)) = r • (a • (x : M))
    exact smul_comm a r (x : M)

end SerrePositivity.DerivedCompletion

end PowerTorsionTowerPart

section PowerTorsionComplexPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Termwise a-power torsion, with the original differential restricted to kernels. -/
abbrev powerTorsionComplex (n : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ where
  X i := ModuleCat.of R (powerTorsionModule a (K.X i) n)
  d i j := ModuleCat.ofHom
    { toFun := fun x ↦ ⟨K.d i j x, by
        change a ^ n • K.d i j (x : K.X i) = 0
        rw [← map_smul]
        exact congrArg (K.d i j) (show a ^ n • (x : K.X i) = 0 from x.property) |>.trans
          (map_zero _)⟩
      map_add' := fun x y ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun r x ↦ Subtype.ext (map_smul _ _ _) }
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f ↦ f.hom (x : K.X i)) (K.shape i j hij)
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f ↦ f.hom (x : K.X i)) (K.d_comp_d i j k)

/-- The actual torsion tower is connected by multiplication by a. -/
def powerTorsionComplexTransition (n : ℕ) :
    powerTorsionComplex a K (n + 1) ⟶ powerTorsionComplex a K n where
  f i := ModuleCat.ofHom (powerTorsionTransition a (K.X i) n)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact map_smul (K.d i j).hom a (x : K.X i)

/-- Complex composites retain the concrete a^k action in each degree. -/
theorem powerTorsionComplexComposite_coe (n k : ℕ) (i : ℤ)
    (x : (powerTorsionComplex a K (n + k)).X i) :
    (((complexTowerComposite R (powerTorsionComplex a K)
      (powerTorsionComplexTransition a K) n k).f i x :
      (powerTorsionComplex a K n).X i) : K.X i) = a ^ k • (x : K.X i) := by
  induction k with
  | zero => simp [complexTowerComposite]
  | succ k ih =>
    change (((complexTowerComposite R (powerTorsionComplex a K)
      (powerTorsionComplexTransition a K) n k).f i
      ((powerTorsionComplexTransition a K (n + k)).f i x) :
      (powerTorsionComplex a K n).X i) : K.X i) = _
    rw [ih]
    change a ^ k • (a • (x : K.X i)) = _
    rw [smul_smul, ← pow_succ]

/-- The coefficient ring's uniform torsion bound kills the torsion error holim
of every termwise flat complex, including unbounded complexes. -/
theorem powerTorsionComplex_holim_acyclic
    (hK : ∀ i, Module.Flat R (K.X i)) (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0) :
    (complexTowerHomotopyLimit R (powerTorsionComplex a K)
      (powerTorsionComplexTransition a K)).Acyclic := by
  apply complexTowerHolim_acyclic_of_uniform_zero R _ _ N
  intro n
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (((complexTowerComposite R (powerTorsionComplex a K)
    (powerTorsionComplexTransition a K) n N).f i x :
    (powerTorsionComplex a K n).X i) : K.X i) = 0
  rw [powerTorsionComplexComposite_coe]
  let := hK i
  exact flat_power_torsion_bound a N h (n + N) (x : K.X i) x.property

end SerrePositivity.DerivedCompletion

end PowerTorsionComplexPart

section PowerImageTowerPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The ordinary cokernel complex; no regularity hypothesis is imposed. -/
abbrev powerCokernelComplex (n : ℕ) := cokernel (smulId (a ^ n) K)

/-- The image complex, keeping the actual differential and categorical image. -/
abbrev powerImageComplex (n : ℕ) := Abelian.image (smulId (a ^ n) K)

/-- Standard transition square: a on the source and identity on the target. -/
lemma powerScalar_square (n : ℕ) :
    smulId a K ≫ smulId (a ^ n) K = smulId (a ^ (n + 1)) K ≫ 𝟙 K := by
  simp [smulId, Linear.comp_smul, smul_smul, pow_succ, mul_comm]

def powerCokernelComplexTransition (n : ℕ) :
    powerCokernelComplex a K (n + 1) ⟶ powerCokernelComplex a K n :=
  cokernel.map _ _ (smulId a K) (𝟙 K) (powerScalar_square a K n).symm

def powerImageComplexTransition (n : ℕ) :
    powerImageComplex a K (n + 1) ⟶ powerImageComplex a K n :=
  kernel.map _ _ (𝟙 K) (powerCokernelComplexTransition a K n) (by
    simp [powerCokernelComplexTransition])

@[reassoc] lemma powerImageComplexTransition_ι (n : ℕ) :
    powerImageComplexTransition a K n ≫ Abelian.image.ι (smulId (a ^ n) K) =
      Abelian.image.ι (smulId (a ^ (n + 1)) K) := by
  simp [powerImageComplexTransition]

@[reassoc] lemma powerImageComplexTransition_factor (n : ℕ) :
    smulId a K ≫ Abelian.factorThruImage (smulId (a ^ n) K) =
      Abelian.factorThruImage (smulId (a ^ (n + 1)) K) ≫ powerImageComplexTransition a K n := by
  apply (cancel_mono (Abelian.image.ι (smulId (a ^ n) K))).mp
  simp only [Category.assoc, powerImageComplexTransition_ι, Abelian.image.fac]
  simpa using powerScalar_square a K n

/-- The original inclusion of termwise torsion into the original complex. -/
def powerTorsionComplexInclusion (n : ℕ) : powerTorsionComplex a K n ⟶ K where
  f i := ModuleCat.ofHom (powerTorsionModule a (K.X i) n).subtype
  comm' _ _ _ := rfl

@[reassoc] lemma powerTorsionComplexInclusion_transition (n : ℕ) :
    powerTorsionComplexTransition a K n ≫ powerTorsionComplexInclusion a K n =
      powerTorsionComplexInclusion a K (n + 1) ≫ smulId a K := rfl

lemma powerTorsionComplexInclusion_factor_zero (n : ℕ) :
    powerTorsionComplexInclusion a K n ≫ Abelian.factorThruImage (smulId (a ^ n) K) = 0 := by
  apply (cancel_mono (Abelian.image.ι (smulId (a ^ n) K))).mp
  rw [Category.assoc, Abelian.image.fac, zero_comp]
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact x.property

/-- Torsion → original complex → image is a genuine short complex. -/
abbrev powerTorsionImageShortComplex (n : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (powerTorsionComplexInclusion a K n)
    (Abelian.factorThruImage (smulId (a ^ n) K)) (powerTorsionComplexInclusion_factor_zero a K n)

lemma powerTorsionImageShortComplex_shortExact (n : ℕ) :
    (powerTorsionImageShortComplex a K n).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change (Abelian.factorThruImage (smulId (a ^ n) K)).f i x = 0 at hx
    have hfac := congrArg (fun f ↦ (f.f i).hom x) (Abelian.image.fac (smulId (a ^ n) K))
    have hscalar : a ^ n • x = 0 := by
      change ((Abelian.image.ι (smulId (a ^ n) K)).f i)
        ((Abelian.factorThruImage (smulId (a ^ n) K)).f i x) = a ^ n • x at hfac
      rw [hx, map_zero] at hfac
      exact hfac.symm
    exact ⟨⟨x, hscalar⟩, rfl⟩
  · exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  · change Epi ((Abelian.factorThruImage (smulId (a ^ n) K)).f i)
    infer_instance

/-- Image → original complex → ordinary cokernel is short exact. -/
abbrev powerImageCokernelShortComplex (n : ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (Abelian.image.ι (smulId (a ^ n) K)) (cokernel.π (smulId (a ^ n) K))
    (kernel.condition _)

lemma powerImageCokernelShortComplex_shortExact (n : ℕ) :
    (powerImageCokernelShortComplex a K n).ShortExact :=
  { exact := ShortComplex.exact_kernel _, mono_f := inferInstance, epi_g := inferInstance }

end SerrePositivity.DerivedCompletion

end PowerImageTowerPart

section PowerCokernelReconstructionPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The torsion, scalar, and image towers form a short exact sequence after holim. -/
abbrev powerTorsionImageHolimShortComplex :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  complexTowerHomotopyLimitShortComplex R
    (powerTorsionComplexTransition a K) (fun _ ↦ smulId a K)
    (powerImageComplexTransition a K) (powerTorsionComplexInclusion a K)
    (fun n ↦ Abelian.factorThruImage (smulId (a ^ n) K))
    (powerTorsionComplexInclusion_transition a K) (powerImageComplexTransition_factor a K)
    (powerTorsionComplexInclusion_factor_zero a K)

lemma powerTorsionImageHolimShortComplex_shortExact :
    (powerTorsionImageHolimShortComplex a K).ShortExact :=
  complexTowerHomotopyLimitShortComplex_shortExact R _ _ _ _ _ _ _ _
    (powerTorsionImageShortComplex_shortExact a K)

/-- For a complete termwise flat complex, the holim of its actual image tower is acyclic. -/
theorem powerImageComplex_holim_acyclic (hK : ∀ i, Module.Flat R (K.X i))
    (N : ℕ) (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (hc : IsComplete R a (DerivedCategory.Q.obj K)) :
    (complexTowerHomotopyLimit R (powerImageComplex a K)
      (powerImageComplexTransition a K)).Acyclic := by
  have hT := powerTorsionComplex_holim_acyclic a K hK N h
  have hS := scalarComplexTowerHomotopyLimit_acyclic_of_isComplete R a K hc
  have he := powerTorsionImageHolimShortComplex_shortExact a K
  intro i
  apply (exactAt_iff_isZero_homology _ i).mpr
  exact (he.homology_exact₃ i (i + 1) rfl).isZero_of_both_isZero
    (hS i).isZero_homology (hT (i + 1)).isZero_homology

@[reassoc] lemma powerCokernelComplexTransition_π (n : ℕ) :
    cokernel.π (smulId (a ^ (n + 1)) K) ≫ powerCokernelComplexTransition a K n =
      cokernel.π (smulId (a ^ n) K) := by
  simp [powerCokernelComplexTransition]

/-- The image, constant, and ordinary cokernel towers form a short exact sequence after holim. -/
abbrev powerImageCokernelHolimShortComplex :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  complexTowerHomotopyLimitShortComplex R
    (powerImageComplexTransition a K) (fun _ ↦ 𝟙 K) (powerCokernelComplexTransition a K)
    (fun n ↦ Abelian.image.ι (smulId (a ^ n) K)) (fun n ↦ cokernel.π (smulId (a ^ n) K))
    (fun n ↦ by simpa using powerImageComplexTransition_ι a K n)
    (fun n ↦ by simpa using (powerCokernelComplexTransition_π a K n).symm)
    (fun n ↦ kernel.condition _)

lemma powerImageCokernelHolimShortComplex_shortExact :
    (powerImageCokernelHolimShortComplex a K).ShortExact :=
  complexTowerHomotopyLimitShortComplex_shortExact R _ _ _ _ _ _ _ _
    (powerImageCokernelShortComplex_shortExact a K)

/-- The canonical map from a complex to the holim of its ordinary power cokernels. -/
def powerCokernelReconstruction :
    K ⟶ complexTowerHomotopyLimit R (powerCokernelComplex a K)
      (powerCokernelComplexTransition a K) :=
  constantComplexTowerUnit R K ≫ (powerImageCokernelHolimShortComplex a K).g

/-- The reconstruction uses the original quotient maps at every stage. -/
lemma powerCokernelReconstruction_eq_lift :
    powerCokernelReconstruction a K =
      complexTowerCompatibleLift R (powerCokernelComplex a K) (powerCokernelComplexTransition a K)
        K (fun n ↦ cokernel.π (smulId (a ^ n) K))
        (powerCokernelComplexTransition_π a K) := by
  unfold powerCokernelReconstruction constantComplexTowerUnit
  apply complexTowerCompatibleLift_map
  intro n
  simp

@[reassoc] lemma powerCokernelReconstruction_projection (n : ℕ) :
    powerCokernelReconstruction a K ≫
      complexTowerProjection R (powerCokernelComplex a K) (powerCokernelComplexTransition a K) ≫
        Pi.π (powerCokernelComplex a K) n = cokernel.π (smulId (a ^ n) K) := by
  rw [powerCokernelReconstruction_eq_lift, ← Category.assoc,
    complexTowerCompatibleLift_comp_projection, Pi.lift_comp_π]

/-- With bounded ring torsion, this actual standard map is a quasi-isomorphism
for every complete termwise flat complex. -/
theorem powerCokernelReconstruction_quasiIso (hK : ∀ i, Module.Flat R (K.X i))
    (N : ℕ) (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (hc : IsComplete R a (DerivedCategory.Q.obj K)) :
    QuasiIso (powerCokernelReconstruction a K) := by
  have hJ := powerImageComplex_holim_acyclic a K hK N h hc
  let S := powerImageCokernelHolimShortComplex a K
  have hS := powerImageCokernelHolimShortComplex_shortExact a K
  have hz : IsZero (DerivedCategory.Q.obj S.X₁) := by
    have hzero := HomologicalComplex.acyclic_of_isZero
      (0 : CochainComplex (ModuleCat.{u} R) ℤ)
      (isZero_zero (CochainComplex (ModuleCat.{u} R) ℤ))
    have : QuasiIso (0 : S.X₁ ⟶ 0) := by
      rw [quasiIso_iff]
      intro i
      exact (quasiIsoAt_iff_exactAt _ i (hJ i)).mpr (hzero i)
    exact (DerivedCategory.Q.map_isZero (isZero_zero _)).of_iso
      (asIso (DerivedCategory.Q.map (0 : S.X₁ ⟶ 0)))
  have hg : IsIso (DerivedCategory.Q.map S.g) :=
    (CategoryTheory.Pretriangulated.Triangle.isZero₁_iff_isIso₂
      (DerivedCategory.triangleOfSES hS) (DerivedCategory.triangleOfSES_distinguished hS)).mp hz
  have : QuasiIso S.g := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp hg
  have := constantComplexTowerUnit_quasiIso R K
  exact inferInstanceAs (QuasiIso (constantComplexTowerUnit R K ≫ S.g))

end SerrePositivity.DerivedCompletion

end PowerCokernelReconstructionPart

section PowerCokernelNaturalityPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] (a : R)
  {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The map of the actual power cokernels, induced by the original complex map. -/
def powerCokernelMap (f : K ⟶ L) (n : ℕ) :
    powerCokernelComplex a K n ⟶ powerCokernelComplex a L n :=
  cokernel.map _ _ f f (by simp [smulId, Linear.smul_comp, Linear.comp_smul])

@[reassoc] lemma powerCokernelMap_π (f : K ⟶ L) (n : ℕ) :
    cokernel.π (smulId (a ^ n) K) ≫ powerCokernelMap a f n =
      f ≫ cokernel.π (smulId (a ^ n) L) := by
  simp [powerCokernelMap, cokernel.map]

@[reassoc] lemma powerCokernelMap_transition (f : K ⟶ L) (n : ℕ) :
    powerCokernelComplexTransition a K n ≫ powerCokernelMap a f n =
      powerCokernelMap a f (n + 1) ≫ powerCokernelComplexTransition a L n := by
  apply (cancel_epi (cokernel.π (smulId (a ^ (n + 1)) K))).mp
  rw [← Category.assoc, powerCokernelComplexTransition_π, powerCokernelMap_π,
    ← Category.assoc, powerCokernelMap_π, Category.assoc, powerCokernelComplexTransition_π]

/-- The original tower map for an arbitrary coefficient-complex map. -/
def powerCokernelHolimMap (f : K ⟶ L) :
    complexTowerHomotopyLimit R (powerCokernelComplex a K) (powerCokernelComplexTransition a K) ⟶
      complexTowerHomotopyLimit R (powerCokernelComplex a L) (powerCokernelComplexTransition a L) :=
  complexTowerHomotopyLimitMap R _ _ (powerCokernelMap a f) (powerCokernelMap_transition a f)

/-- Reconstruction intertwines arbitrary original complex maps and their holim maps. -/
@[reassoc] lemma powerCokernelReconstruction_naturality (f : K ⟶ L) :
    powerCokernelReconstruction a K ≫ powerCokernelHolimMap a f =
      f ≫ powerCokernelReconstruction a L := by
  rw [powerCokernelReconstruction_eq_lift, powerCokernelReconstruction_eq_lift]
  exact complexTowerCompatibleLift_naturality R _ _ _ _ _ f _ _ _ _ (powerCokernelMap_π a f)

end SerrePositivity.DerivedCompletion

end PowerCokernelNaturalityPart

section PowerCokernelTensorModelPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R] (a : R)

/-- The original R-linear quotient map, including the zeroth power quotient. -/
def powerQuotientCoefficientMap (n : ℕ) :
    ModuleCat.of R R ⟶ ModuleCat.of R (R ⧸ Ideal.span {a ^ n}) :=
  ModuleCat.ofHom (Ideal.Quotient.mkₐ R (Ideal.span {a ^ n})).toLinearMap

instance powerQuotientCoefficientMap_epi (n : ℕ) : Epi (powerQuotientCoefficientMap a n) :=
  (ModuleCat.epi_iff_surjective _).mpr Ideal.Quotient.mk_surjective

abbrev powerQuotientCoefficientShortComplex (n : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (a ^ n • 𝟙 (ModuleCat.of R R)) (powerQuotientCoefficientMap a n) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Ideal.Quotient.mk (Ideal.span {a ^ n}) (a ^ n * r) = 0
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.mem_span_singleton.mpr ⟨r, rfl⟩)

lemma powerQuotientCoefficientShortComplex_exact (n : ℕ) :
    (powerQuotientCoefficientShortComplex a n).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  change Ideal.Quotient.mk (Ideal.span {a ^ n}) x = 0 at hx
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp hx)
  exact ⟨r, hr.symm⟩

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The standard quotient-coefficient map on the original complex. -/
def powerQuotientTensorMap (n : ℕ) :
    K ⟶ (moduleTensorCochainFunctor K).obj (ModuleCat.of R (R ⧸ Ideal.span {a ^ n})) :=
  (moduleTensorCochainUnitIso K).inv ≫
    (moduleTensorCochainFunctor K).map (powerQuotientCoefficientMap a n)

lemma powerQuotientTensorMap_zero (n : ℕ) :
    smulId (a ^ n) K ≫ powerQuotientTensorMap a K n = 0 := by
  let F := moduleTensorCochainFunctor K
  let e := moduleTensorCochainUnitIso K
  calc
    smulId (a ^ n) K ≫ powerQuotientTensorMap a K n =
        e.inv ≫ (F.map (a ^ n • 𝟙 (ModuleCat.of R R)) ≫
          F.map (powerQuotientCoefficientMap a n)) := by
      simp [powerQuotientTensorMap, F, e, smulId, Linear.smul_comp, Linear.comp_smul]
    _ = 0 := by
      rw [← F.map_comp, (powerQuotientCoefficientShortComplex a n).zero, F.map_zero, comp_zero]

abbrev powerQuotientTensorShortComplex (n : ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (smulId (a ^ n) K) (powerQuotientTensorMap a K n)
    (powerQuotientTensorMap_zero a K n)

lemma powerQuotientTensorShortComplex_exact (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    (powerQuotientTensorShortComplex a K n).Exact := by
  let F := moduleTensorCochainFunctor K
  let e := moduleTensorCochainUnitIso K
  let hS := moduleTensorCochain_exact K hK (powerQuotientCoefficientShortComplex a n)
    (powerQuotientCoefficientShortComplex_exact a n)
  let ei : (powerQuotientCoefficientShortComplex a n).map F ≅
      powerQuotientTensorShortComplex a K n :=
    ShortComplex.isoMk e e (Iso.refl _)
      (by simp [smulId, F, Linear.comp_smul, Linear.smul_comp])
      (by simp [powerQuotientTensorMap, e, F])
  exact ShortComplex.exact_of_iso ei hS

instance powerQuotientTensorMap_epi (n : ℕ) : Epi (powerQuotientTensorMap a K n) := by
  have := moduleTensorCochain_map_epi K (powerQuotientCoefficientMap a n)
  dsimp only [powerQuotientTensorMap]
  infer_instance

/-- In a flat model, the actual categorical cokernel equals tensoring the
original model with the ordinary quotient module. -/
def powerCokernelTensorModelIso (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    powerCokernelComplex a K n ≅
      (moduleTensorCochainFunctor K).obj (ModuleCat.of R (R ⧸ Ideal.span {a ^ n})) :=
  (cokernelIsCokernel (smulId (a ^ n) K)).coconePointUniqueUpToIso
    (powerQuotientTensorShortComplex_exact a K hK n).gIsCokernel

@[reassoc] lemma powerCokernelTensorModelIso_π (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    cokernel.π (smulId (a ^ n) K) ≫ (powerCokernelTensorModelIso a K hK n).hom =
      powerQuotientTensorMap a K n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (smulId (a ^ n) K))
    (powerQuotientTensorShortComplex_exact a K hK n).gIsCokernel WalkingParallelPair.one

end SerrePositivity.DerivedCompletion

end PowerCokernelTensorModelPart

section PowerCokernelTransitionsPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)

lemma powerPrincipalIdeal_antitone_step (n : ℕ) :
    Ideal.span {a ^ (n + 1)} ≤ Ideal.span {a ^ n} :=
  (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr ⟨a, pow_succ a n⟩)

def powerQuotientCoefficientTransition (n : ℕ) :
    ModuleCat.of R (R ⧸ Ideal.span {a ^ (n + 1)}) ⟶ ModuleCat.of R (R ⧸ Ideal.span {a ^ n}) :=
  ModuleCat.ofHom (Ideal.Quotient.factorₐ R (powerPrincipalIdeal_antitone_step a n)).toLinearMap

@[reassoc] lemma powerQuotientCoefficientMap_transition (n : ℕ) :
    powerQuotientCoefficientMap a (n + 1) ≫ powerQuotientCoefficientTransition a n =
      powerQuotientCoefficientMap a n := rfl

instance powerQuotientCoefficientTransition_epi (n : ℕ) :
    Epi (powerQuotientCoefficientTransition a n) :=
  epi_of_epi_fac (powerQuotientCoefficientMap_transition a n)

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The original cokernel transitions agree with the original quotient module maps. -/
@[reassoc] lemma powerCokernelTensorModelIso_transition
    (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    powerCokernelComplexTransition a K n ≫ (powerCokernelTensorModelIso a K hK n).hom =
      (powerCokernelTensorModelIso a K hK (n + 1)).hom ≫
        (moduleTensorCochainFunctor K).map (powerQuotientCoefficientTransition a n) := by
  apply (cancel_epi (cokernel.π (smulId (a ^ (n + 1)) K))).mp
  rw [← Category.assoc, powerCokernelComplexTransition_π, powerCokernelTensorModelIso_π]
  rw [← Category.assoc, powerCokernelTensorModelIso_π]
  simp only [powerQuotientTensorMap, Category.assoc, ← Functor.map_comp,
    powerQuotientCoefficientMap_transition]

/-- The H0 transitions of the actual cokernel tower are surjective under the
original pure flat mod-a input, including the zero-power stage. -/
lemma powerCokernel_homology_zero_transition_surjective
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (hPure : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
    (hFlat : Module.Flat (R ⧸ Ideal.span {a})
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj)) (n : ℕ) :
    Function.Surjective (homologyMap
      (powerCokernelComplexTransition a (boundedAboveDerivedChosenModel X).complex n) 0) := by
  let P := (boundedAboveDerivedChosenModel X).complex
  have hP : ∀ i, Module.Flat R (P.X i) := by
    intro i
    have : Module.Projective R (P.X i) := inferInstance
    infer_instance
  have hs := modelTensor_homology_zero_map_surjective_of_power_annihilated a X hPure hFlat
    (n + 1) (powerQuotientCoefficientTransition a n) (fun x ↦ by
      change Ideal.Quotient.mk (Ideal.span {a ^ (n + 1)}) (a ^ (n + 1)) * x = 0
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _), zero_mul])
  let H := homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
  have he : Epi (H.map ((moduleTensorCochainFunctor P).map
      (powerQuotientCoefficientTransition a n))) := (ModuleCat.epi_iff_surjective _).mpr hs
  have hw := congrArg H.map (powerCokernelTensorModelIso_transition a P hP n)
  simp only [Functor.map_comp] at hw
  have ht : Epi (H.map (powerCokernelComplexTransition a P n) ≫
      H.map (powerCokernelTensorModelIso a P hP n).hom) := by
    rw [hw]
    infer_instance
  have := (epi_comp_iff_of_isIso (H.map (powerCokernelComplexTransition a P n))
    (H.map (powerCokernelTensorModelIso a P hP n).hom)).mp ht
  exact (ModuleCat.epi_iff_surjective _).mp this

end SerrePositivity.DerivedCompletion

end PowerCokernelTransitionsPart

section KoszulPowerCokernelComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)

abbrev powerScalarCokernelShortComplex (n : ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (smulId (a ^ n) K) (cokernel.π (smulId (a ^ n) K)) (cokernel.condition _)

/-- The actual standard augmentation; it need not be a quasi-isomorphism at a stage. -/
def koszulPowerCokernelAugmentation (n : ℕ) :
    complexPowerKoszulStage R a K n ⟶ powerCokernelComplex a K n :=
  CochainComplex.mappingCone.descShortComplex (powerScalarCokernelShortComplex a K n)

@[reassoc] lemma koszulPowerCokernelAugmentation_inr (n : ℕ) :
    CochainComplex.mappingCone.inr (smulId (a ^ n) K) ≫
      koszulPowerCokernelAugmentation a K n = cokernel.π (smulId (a ^ n) K) := by
  apply CochainComplex.mappingCone.inr_descShortComplex

lemma koszulPowerCokernelAugmentation_transition (n : ℕ) :
    complexPowerKoszulTransition R a K n ≫ koszulPowerCokernelAugmentation a K n =
      koszulPowerCokernelAugmentation a K (n + 1) ≫ powerCokernelComplexTransition a K n := by
  let f : powerScalarCokernelShortComplex a K (n + 1) ⟶ powerScalarCokernelShortComplex a K n :=
    { τ₁ := smulId a K
      τ₂ := 𝟙 K
      τ₃ := powerCokernelComplexTransition a K n
      comm₁₂ := powerScalar_square a K n
      comm₂₃ := by simpa using (powerCokernelComplexTransition_π a K n).symm }
  have hm : complexPowerKoszulTransition R a K n =
      CochainComplex.mappingCone.map (smulId (a ^ (n + 1)) K) (smulId (a ^ n) K)
        (a • 𝟙 K) (𝟙 K) (powerScalar_square a K n).symm :=
    cochainMappingConeFunctor_map_eq R
      (X := Arrow.mk (smulId (a ^ (n + 1)) K)) (Y := Arrow.mk (smulId (a ^ n) K))
      (Arrow.homMk (a • 𝟙 K) (𝟙 K) (powerScalar_square a K n))
  rw [hm]
  have hn := CochainComplex.mappingCone.map_descShortComplex
    (powerScalarCokernelShortComplex a K (n + 1)) (powerScalarCokernelShortComplex a K n) f
  exact hn

/-- The standard augmentation of towers induces this actual chain map on holims. -/
def koszulPowerCokernelComparison :
    (complexCompletionFunctor R a).obj K ⟶
      complexTowerHomotopyLimit R (powerCokernelComplex a K) (powerCokernelComplexTransition a K) :=
  complexTowerHomotopyLimitMap R (complexPowerKoszulTransition R a K)
    (powerCokernelComplexTransition a K) (koszulPowerCokernelAugmentation a K)
    (koszulPowerCokernelAugmentation_transition a K)

@[reassoc] lemma complexCompletionUnit_comp_koszulPowerCokernelComparison :
    complexCompletionUnit R a K ≫ koszulPowerCokernelComparison a K =
      powerCokernelReconstruction a K := by
  rw [powerCokernelReconstruction_eq_lift]
  apply complexTowerCompatibleLift_map
  exact koszulPowerCokernelAugmentation_inr a K

end SerrePositivity.DerivedCompletion

end KoszulPowerCokernelComparisonPart

section PowerTowerLimitBoundPart

namespace SerrePositivity.DerivedCompletion
variable {R : Type u} [CommRing R] (a : R) (N : ℕ)
    (M : ℕ → Type v) [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    (t : ∀ j, M (j + 1) →ₗ[R] M j)

/-- This formulation needs only R-linear relations, so it applies to models
compared with flat quotient modules without transporting module instances. -/
theorem moduleTowerLimit_power_torsion_bound_of_relations
    (hKill : ∀ j, ∀ z : M j, a ^ j • z = 0)
    (hRel : ∀ j m, ∀ z : M (j + m), a ^ m • z = 0 →
      ∃ y : M (j + m), a ^ N • z = a ^ j • y) :
    ∀ m : ℕ, ∀ x : moduleTowerLimit R M t, a ^ m • x = 0 → a ^ N • x = 0 := by
  intro m x hx
  apply Subtype.ext
  funext j
  let f : ∀ k : ℕ, M (j + k) →ₗ[R] M j := fun k ↦
    Nat.rec (motive := fun k ↦ M (j + k) →ₗ[R] M j) LinearMap.id
      (fun k g ↦ g.comp (t (j + k))) k
  have hf : ∀ k, f k (x.val (j + k)) = x.val j := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change f k (t (j + k) (x.val (j + k + 1))) = x.val j
      rw [(mem_moduleTowerLimit_iff R M t _).mp x.property (j + k), ih]
  obtain ⟨y, hy⟩ := hRel j m (x.val (j + m)) (congrArg (fun y ↦ y.val (j + m)) hx)
  have he := congrArg (f m) hy
  change a ^ N • x.val j = 0
  simpa only [map_smul, hf, hKill] using he

end SerrePositivity.DerivedCompletion

end PowerTowerLimitBoundPart
