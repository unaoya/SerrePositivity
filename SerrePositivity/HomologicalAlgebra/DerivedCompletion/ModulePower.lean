module

public import SerrePositivity.CommutativeAlgebra.Adic.Reduction
public import SerrePositivity.CommutativeAlgebra.Adic.Principal
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTower
public import SerrePositivity.HomologicalAlgebra.DerivedTensorFixedModuleModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Maps
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Flat.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TermwiseComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleClosure
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ReflectionTransport
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison
public import SerrePositivity.HomologicalAlgebra.Resolution.FiniteFree
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedTensorUnresolvedModule
public import SerrePositivity.HomologicalAlgebra.DerivedTensorSymmetry
public import SerrePositivity.HomologicalAlgebra.DerivedTensorTorNaturality
public import SerrePositivity.HomologicalAlgebra.KoszulTorComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Milnor

/-! # 加群の冪商の塔と導来テンソルの再構成

## 概要

任意の加群 M の通常の冪商 M/aⁿM の塔と標準写像を作り、平坦なテンソルのモデルの中で冪商を表して、導来テンソル C ⊗ᴸ M/aⁿM（元の商写像と遷移写像つき）と比較する。完備な係数 C について、通常の冪商のテンソルの塔の holim から C ⊗ᴸ M を再構成し（係数の射との自然性つき）、冪の余核の塔と Tor の係数作用を比べる。M の冪ねじれの有界性（係数環ではなく試験加群の性質）や、項の冪ねじれの共通の上界から再構成でき、有限な係数とのテンソルは導来完備である（`FiniteTensorComplete`）。

## 方針

C を分解して M は分解しないまま、各段の比較を導来圏で取り、holim の短完全列と Milnor 列で全体を組み立てる。元の環の有界ねじれや項の平坦性は仮定しない。

## 規約

試験加群 M はねじれを持ってよい。係数の射は R 代数の元による掛け算でもよい。

## 使われ方

CLMST の完備テンソルの同種写像と有限段の比較、`TorAlgebraComplete`。
-/

@[expose] public noncomputable section

universe u

section ModulePowerReductionPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] (a : R) (M : ModuleCat.{u} R)

/-- The ordinary quotient M/aⁿM, with its original restricted R-action. -/
abbrev modulePowerReduction (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (AdicReduction (Ideal.span {a ^ n}) M)

/-- The original ordinary quotient map. -/
def modulePowerReductionMap (n : ℕ) : M ⟶ modulePowerReduction a M n :=
  ModuleCat.ofHom (Ideal.span {a ^ n} • (⊤ : Submodule R M)).mkQ

instance modulePowerReductionMap_epi (n : ℕ) : Epi (modulePowerReductionMap a M n) :=
  (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

/-- The reduction is killed by the specified power, without any torsion condition on M. -/
lemma modulePowerReduction_pow_smul_zero (n : ℕ) (x : modulePowerReduction a M n) :
    a ^ n • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change (Ideal.span {a ^ n} • (⊤ : Submodule R M)).mkQ (a ^ n • x) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) Submodule.mem_top

lemma modulePowerReductionMap_zero (n : ℕ) :
    (a ^ n • 𝟙 M) ≫ modulePowerReductionMap a M n = 0 := by
  ext x
  exact modulePowerReduction_pow_smul_zero a M n (modulePowerReductionMap a M n x)

/-- Scalar multiplication followed by the original quotient is an exact sequence. -/
abbrev modulePowerReductionShortComplex (n : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (a ^ n • 𝟙 M) (modulePowerReductionMap a M n)
    (modulePowerReductionMap_zero a M n)

lemma modulePowerReductionShortComplex_exact (n : ℕ) :
    (modulePowerReductionShortComplex a M n).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hx' : x ∈ Ideal.span {a ^ n} • (⊤ : Submodule R M) :=
    (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨y, hy⟩ := (mem_principal_pow_smul_top a n x).mp
    (by simpa only [Ideal.span_singleton_pow] using hx')
  exact ⟨y, hy⟩

/-- The ordinary reduction transition is induced by the identity of M. -/
def modulePowerReductionTransition (n : ℕ) :
    modulePowerReduction a M (n + 1) ⟶ modulePowerReduction a M n :=
  ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id (by
    intro x hx
    obtain ⟨y, hy⟩ := (mem_principal_pow_smul_top a (n + 1) x).mp
      (by simpa only [Ideal.span_singleton_pow] using hx)
    change x ∈ Ideal.span {a ^ n} • (⊤ : Submodule R M)
    rw [← hy]
    have he : a ^ (n + 1) • y = a ^ n • (a • y) := by rw [pow_succ, mul_smul]
    rw [he]
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _))
      Submodule.mem_top))

@[reassoc] lemma modulePowerReductionTransition_π (n : ℕ) :
    modulePowerReductionMap a M (n + 1) ≫ modulePowerReductionTransition a M n =
      modulePowerReductionMap a M n := by
  ext x
  rfl

instance modulePowerReductionTransition_epi (n : ℕ) :
    Epi (modulePowerReductionTransition a M n) :=
  epi_of_epi_fac (modulePowerReductionTransition_π a M n)

end SerrePositivity.DerivedCompletion

end ModulePowerReductionPart

section ModulePowerTensorModelPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R] (a : R) (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Tensor the original map M → M/aⁿM with the same complex K. -/
def modulePowerTensorReductionMap (n : ℕ) :
    (moduleTensorCochainFunctor K).obj M ⟶
      (moduleTensorCochainFunctor K).obj (modulePowerReduction a M n) :=
  (moduleTensorCochainFunctor K).map (modulePowerReductionMap a M n)

lemma modulePowerTensorReductionMap_zero (n : ℕ) :
    smulId (a ^ n) ((moduleTensorCochainFunctor K).obj M) ≫
      modulePowerTensorReductionMap a M K n = 0 := by
  let F := moduleTensorCochainFunctor K
  have he : smulId (a ^ n) (F.obj M) = F.map (a ^ n • 𝟙 M) := by
    simp [smulId]
  rw [he]
  change F.map (a ^ n • 𝟙 M) ≫ F.map (modulePowerReductionMap a M n) = 0
  rw [← F.map_comp, modulePowerReductionMap_zero, F.map_zero]

abbrev modulePowerTensorReductionShortComplex (n : ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (smulId (a ^ n) ((moduleTensorCochainFunctor K).obj M))
    (modulePowerTensorReductionMap a M K n) (modulePowerTensorReductionMap_zero a M K n)

lemma modulePowerTensorReductionShortComplex_exact
    (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    (modulePowerTensorReductionShortComplex a M K n).Exact := by
  let F := moduleTensorCochainFunctor K
  let e : (modulePowerReductionShortComplex a M n).map F ≅
      modulePowerTensorReductionShortComplex a M K n :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [smulId, F]) (by simp [modulePowerTensorReductionMap, F])
  exact ShortComplex.exact_of_iso e
    (moduleTensorCochain_exact K hK _ (modulePowerReductionShortComplex_exact a M n))

instance modulePowerTensorReductionMap_epi (n : ℕ) :
    Epi (modulePowerTensorReductionMap a M K n) :=
  moduleTensorCochain_map_epi K (modulePowerReductionMap a M n)

/-- Each ordinary power cokernel in M ⊗ K is the actual tensor of M/aⁿM with K. -/
def modulePowerTensorModelIso (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    powerCokernelComplex a ((moduleTensorCochainFunctor K).obj M) n ≅
      (moduleTensorCochainFunctor K).obj (modulePowerReduction a M n) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    (modulePowerTensorReductionShortComplex_exact a M K hK n).gIsCokernel

@[reassoc] lemma modulePowerTensorModelIso_π
    (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    cokernel.π (smulId (a ^ n) ((moduleTensorCochainFunctor K).obj M)) ≫
      (modulePowerTensorModelIso a M K hK n).hom =
        modulePowerTensorReductionMap a M K n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (modulePowerTensorReductionShortComplex_exact a M K hK n).gIsCokernel
    WalkingParallelPair.one

/-- The comparison identifies the original tower transition with the ordinary
reduction transition induced by the identity of M. -/
@[reassoc] lemma modulePowerTensorModelIso_transition
    (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    powerCokernelComplexTransition a ((moduleTensorCochainFunctor K).obj M) n ≫
        (modulePowerTensorModelIso a M K hK n).hom =
      (modulePowerTensorModelIso a M K hK (n + 1)).hom ≫
        (moduleTensorCochainFunctor K).map (modulePowerReductionTransition a M n) := by
  apply (cancel_epi (cokernel.π
    (smulId (a ^ (n + 1)) ((moduleTensorCochainFunctor K).obj M)))).mp
  rw [← Category.assoc, powerCokernelComplexTransition_π, modulePowerTensorModelIso_π]
  rw [← Category.assoc, modulePowerTensorModelIso_π]
  simp only [modulePowerTensorReductionMap, ← Functor.map_comp,
    modulePowerReductionTransition_π]

variable {K} {L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Changing the fixed complex induces the original cokernel map at each stage. -/
def modulePowerTensorCokernelMap (f : K ⟶ L) (n : ℕ) :
    powerCokernelComplex a ((moduleTensorCochainFunctor K).obj M) n ⟶
      powerCokernelComplex a ((moduleTensorCochainFunctor L).obj M) n :=
  cokernel.map _ _
    (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map f)
    (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map f)
    (by simp [smulId, Linear.smul_comp, Linear.comp_smul])

/-- Naturality includes arbitrary coefficient-resolution maps, hence in
particular the original lifts of multiplication by coefficient scalars. -/
@[reassoc] lemma modulePowerTensorModelIso_naturality
    (f : K ⟶ L) (hK : ∀ i, Module.Flat R (K.X i))
    (hL : ∀ i, Module.Flat R (L.X i)) (n : ℕ) :
    modulePowerTensorCokernelMap a M f n ≫ (modulePowerTensorModelIso a M L hL n).hom =
      (modulePowerTensorModelIso a M K hK n).hom ≫
        (((tensorLeft (modulePowerReduction a M n)).mapHomologicalComplex (.up ℤ)).map f) := by
  apply (cancel_epi (cokernel.π
    (smulId (a ^ n) ((moduleTensorCochainFunctor K).obj M)))).mp
  rw [← Category.assoc]
  simp only [modulePowerTensorCokernelMap, cokernel.map, cokernel.π_desc,
    Category.assoc, modulePowerTensorModelIso_π]
  rw [modulePowerTensorModelIso_π_assoc]
  change (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map f) ≫
      modulePowerTensorReductionMap a M L n =
    modulePowerTensorReductionMap a M K n ≫ _
  exact (NatTrans.mapHomologicalComplex
    ((tensoringLeft (ModuleCat R)).map (modulePowerReductionMap a M n)) (.up ℤ)).naturality f

end SerrePositivity.DerivedCompletion

end ModulePowerTensorModelPart

section ModulePowerDerivedComparisonPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R) (C M : ModuleCat.{u} R)

lemma moduleCoefficientResolution_flat (i : ℤ) :
    Module.Flat R ((extRes (projectiveResolution C)).X i) := by
  have : Module.Projective R ((extRes (projectiveResolution C)).X i) := inferInstance
  infer_instance

/-- Each original power cokernel computes the actual tensor of C with the
ordinary quotient M/aⁿM. No regularity or completeness assumptions are needed. -/
def modulePowerDerivedTensorIso (n : ℕ) :
    DerivedCategory.Q.obj (powerCokernelComplex a
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n) ≅
        (boundedAboveDerivedTensorModuleFunctor C).obj (modulePowerReduction a M n) :=
  DerivedCategory.Q.mapIso (modulePowerTensorModelIso a M
    (extRes (projectiveResolution C)) (moduleCoefficientResolution_flat C) n) ≪≫
      (derivedTensorCoefficientModelIso C (modulePowerReduction a M n)).symm

/-- The actual derived reduction map is the original quotient map under the
comparison, not a map selected after identifying the two objects. -/
@[reassoc] lemma modulePowerDerivedTensorIso_π (n : ℕ) :
    DerivedCategory.Q.map (cokernel.π (smulId (a ^ n)
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M))) ≫
        (modulePowerDerivedTensorIso a C M n).hom =
      (derivedTensorCoefficientModelIso C M).inv ≫
        (boundedAboveDerivedTensorModuleFunctor C).map (modulePowerReductionMap a M n) := by
  let f := modulePowerReductionMap a M n
  let eM := derivedTensorCoefficientModelIso C M
  let eN := derivedTensorCoefficientModelIso C (modulePowerReduction a M n)
  let pf := DerivedCategory.Q.map
    ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).map f)
  have h : pf ≫ eN.inv = eM.inv ≫ (boundedAboveDerivedTensorModuleFunctor C).map f := by
    apply (cancel_epi eM.hom).mp
    rw [← Category.assoc, ← derivedTensorCoefficientModelIso_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  simp only [modulePowerDerivedTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, ← Category.assoc, ← Functor.map_comp, modulePowerTensorModelIso_π]
  exact h

/-- The original power-cokernel transition becomes the actual derived map
induced by M/aⁿ⁺¹M → M/aⁿM. -/
@[reassoc] lemma modulePowerDerivedTensorIso_transition (n : ℕ) :
    DerivedCategory.Q.map (powerCokernelComplexTransition a
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n) ≫
        (modulePowerDerivedTensorIso a C M n).hom =
      (modulePowerDerivedTensorIso a C M (n + 1)).hom ≫
        (boundedAboveDerivedTensorModuleFunctor C).map (modulePowerReductionTransition a M n) := by
  let f := modulePowerReductionTransition a M n
  let eM := derivedTensorCoefficientModelIso C (modulePowerReduction a M (n + 1))
  let eN := derivedTensorCoefficientModelIso C (modulePowerReduction a M n)
  let pf := DerivedCategory.Q.map
    ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).map f)
  have h : pf ≫ eN.inv = eM.inv ≫ (boundedAboveDerivedTensorModuleFunctor C).map f := by
    apply (cancel_epi eM.hom).mp
    rw [← Category.assoc, ← derivedTensorCoefficientModelIso_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have ht := congrArg DerivedCategory.Q.map
    (modulePowerTensorModelIso_transition a M (extRes (projectiveResolution C))
      (moduleCoefficientResolution_flat C) n)
  simp only [Functor.map_comp] at ht
  simp only [modulePowerDerivedTensorIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ht, Category.assoc]
  change _ ≫ (pf ≫ eN.inv) = (_ ≫ eM.inv) ≫ _
  rw [h, Category.assoc]

variable {C} {D : ModuleCat.{u} R}

/-- The derived comparison keeps every coefficient map, using its original
resolution lift; multiplication maps give the Tor actions used by KL. -/
@[reassoc] lemma modulePowerDerivedTensorIso_naturality
    (f : C ⟶ D) (n : ℕ) :
    DerivedCategory.Q.map (modulePowerTensorCokernelMap a M
      (extLift (projectiveResolution C) f (projectiveResolution D)) n) ≫
        (modulePowerDerivedTensorIso a D M n).hom =
      (modulePowerDerivedTensorIso a C M n).hom ≫
        (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map f)
          (𝟙 (boundedAboveDerivedSingleFunctor.obj (modulePowerReduction a M n))))).hom := by
  let N := modulePowerReduction a M n
  let eC := derivedTensorCoefficientModelIso C N
  let eD := derivedTensorCoefficientModelIso D N
  let pf := DerivedCategory.Q.map
    (((MonoidalCategory.tensorLeft N).mapHomologicalComplex (.up ℤ)).map
      (extLift (projectiveResolution C) f (projectiveResolution D)))
  let df := (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
    (boundedAboveDerivedSingleFunctor.map f) (𝟙 (boundedAboveDerivedSingleFunctor.obj N)))).hom
  have h : pf ≫ eD.inv = eC.inv ≫ df := by
    apply (cancel_epi eC.hom).mp
    rw [← Category.assoc, ← derivedTensorCoefficientModelIso_naturality_left,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have ht := congrArg DerivedCategory.Q.map
    (modulePowerTensorModelIso_naturality a M
      (extLift (projectiveResolution C) f (projectiveResolution D))
      (moduleCoefficientResolution_flat C) (moduleCoefficientResolution_flat D) n)
  simp only [Functor.map_comp] at ht
  simp only [modulePowerDerivedTensorIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ht, Category.assoc]
  change _ ≫ (pf ≫ eD.inv) = (_ ≫ eC.inv) ≫ df
  rw [h, Category.assoc]

end SerrePositivity.DerivedCompletion

end ModulePowerDerivedComparisonPart

section BoundedTermTorsionComparisonPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ℕ)
    (h : ∀ (i : ℤ) (n : ℕ) (x : K.X i), a ^ n • x = 0 → a ^ N • x = 0)

include N h

/-- A common termwise bound kills the genuine torsion tower, with its scalar
transitions rather than inclusion maps. -/
lemma powerTorsionComplex_holim_acyclic_of_term_bound :
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
  exact h i (n + N) x x.property

lemma powerImageComplex_holim_acyclic_of_term_bound
    (hc : IsComplete R a (DerivedCategory.Q.obj K)) :
    (complexTowerHomotopyLimit R (powerImageComplex a K)
      (powerImageComplexTransition a K)).Acyclic := by
  have hT := powerTorsionComplex_holim_acyclic_of_term_bound a K N h
  have hS := scalarComplexTowerHomotopyLimit_acyclic_of_isComplete R a K hc
  have he := powerTorsionImageHolimShortComplex_shortExact a K
  intro i
  exact (exactAt_iff_isZero_homology _ i).mpr
    ((he.homology_exact₃ i (i + 1) rfl).isZero_of_both_isZero
      (hS i).isZero_homology (hT (i + 1)).isZero_homology)

/-- The original quotient reconstruction is a quasi-isomorphism for a complete
complex with a common termwise power-torsion bound. -/
lemma powerCokernelReconstruction_quasiIso_of_term_bound
    (hc : IsComplete R a (DerivedCategory.Q.obj K)) :
    QuasiIso (powerCokernelReconstruction a K) := by
  have hJ := powerImageComplex_holim_acyclic_of_term_bound a K N h hc
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

/-- The existing standard augmentation of towers is a quasi-isomorphism, with
the existing completion unit diagram retained. -/
lemma koszulPowerCokernelComparison_quasiIso_of_term_bound
    (hc : IsComplete R a (DerivedCategory.Q.obj K)) :
    QuasiIso (koszulPowerCokernelComparison a K) := by
  have := complexCompletionUnit_quasiIso_of_isComplete R a K hc
  have : QuasiIso (complexCompletionUnit R a K ≫ koszulPowerCokernelComparison a K) := by
    rw [complexCompletionUnit_comp_koszulPowerCokernelComparison]
    exact powerCokernelReconstruction_quasiIso_of_term_bound a K N h hc
  exact (quasiIso_iff_comp_left (complexCompletionUnit R a K) _).mp inferInstance

end SerrePositivity.DerivedCompletion

end BoundedTermTorsionComparisonPart

section ModulePowerTensorHolimPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R) (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The tower consists of the actual ordinary quotients tensored with the fixed model. -/
abbrev modulePowerTensorTower (n : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (moduleTensorCochainFunctor K).obj (modulePowerReduction a M n)

def modulePowerTensorTransition (n : ℕ) :
    modulePowerTensorTower a M K (n + 1) ⟶ modulePowerTensorTower a M K n :=
  (moduleTensorCochainFunctor K).map (modulePowerReductionTransition a M n)

lemma modulePowerTensorReductionMap_transition (n : ℕ) :
    modulePowerTensorReductionMap a M K (n + 1) ≫ modulePowerTensorTransition a M K n =
      modulePowerTensorReductionMap a M K n := by
  simp only [modulePowerTensorReductionMap, modulePowerTensorTransition,
    ← Functor.map_comp, modulePowerReductionTransition_π]

/-- The original compatible quotient maps define the reconstruction itself. -/
def modulePowerTensorReconstruction :
    (moduleTensorCochainFunctor K).obj M ⟶
      complexTowerHomotopyLimit R (modulePowerTensorTower a M K)
        (modulePowerTensorTransition a M K) :=
  complexTowerCompatibleLift R _ _ _ (modulePowerTensorReductionMap a M K)
    (modulePowerTensorReductionMap_transition a M K)

@[reassoc] lemma modulePowerTensorReconstruction_projection (n : ℕ) :
    modulePowerTensorReconstruction a M K ≫
      complexTowerProjection R (modulePowerTensorTower a M K) (modulePowerTensorTransition a M K) ≫
        Pi.π (modulePowerTensorTower a M K) n = modulePowerTensorReductionMap a M K n := by
  rw [modulePowerTensorReconstruction, ← Category.assoc,
    complexTowerCompatibleLift_comp_projection, Pi.lift_comp_π]

/-- The existing ordinary cokernel tower and the actual quotient tensor tower
have canonically isomorphic holims. -/
def modulePowerCokernelHolimIso (hK : ∀ i, Module.Flat R (K.X i)) :
    complexTowerHomotopyLimit R
      (powerCokernelComplex a ((moduleTensorCochainFunctor K).obj M))
      (powerCokernelComplexTransition a ((moduleTensorCochainFunctor K).obj M)) ≅
    complexTowerHomotopyLimit R (modulePowerTensorTower a M K)
      (modulePowerTensorTransition a M K) :=
  complexTowerHomotopyLimitIso R _ _ (modulePowerTensorModelIso a M K hK)
    (modulePowerTensorModelIso_transition a M K hK)

/-- The holim comparison transports the original reconstruction to the original
quotient lift, not just to an isomorphic unspecified map. -/
@[reassoc] lemma powerCokernelReconstruction_comp_modulePowerHolimIso
    (hK : ∀ i, Module.Flat R (K.X i)) :
    powerCokernelReconstruction a ((moduleTensorCochainFunctor K).obj M) ≫
      (modulePowerCokernelHolimIso a M K hK).hom = modulePowerTensorReconstruction a M K := by
  rw [powerCokernelReconstruction_eq_lift]
  exact complexTowerCompatibleLift_iso R _ _ (modulePowerTensorModelIso a M K hK)
    (modulePowerTensorModelIso_transition a M K hK) _ _
    (powerCokernelComplexTransition_π a ((moduleTensorCochainFunctor K).obj M)) _
    (modulePowerTensorReductionMap_transition a M K) (modulePowerTensorModelIso_π a M K hK)

/-- A common torsion bound and actual completeness prove that the standard
quotient lift is a quasi-isomorphism. -/
lemma modulePowerTensorReconstruction_quasiIso
    (hK : ∀ i, Module.Flat R (K.X i)) (N : ℕ)
    (h : ∀ (i : ℤ) (n : ℕ) (x : ((moduleTensorCochainFunctor K).obj M).X i),
      a ^ n • x = 0 → a ^ N • x = 0)
    (hc : IsComplete R a (DerivedCategory.Q.obj ((moduleTensorCochainFunctor K).obj M))) :
    QuasiIso (modulePowerTensorReconstruction a M K) := by
  have := powerCokernelReconstruction_quasiIso_of_term_bound a _ N h hc
  rw [← powerCokernelReconstruction_comp_modulePowerHolimIso a M K hK]
  infer_instance

end SerrePositivity.DerivedCompletion

end ModulePowerTensorHolimPart

section ModulePowerTorsionBoundPart

namespace SerrePositivity
open scoped TensorProduct
variable {R M F : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup F] [Module R F]

/-- Ascending scalar kernels stabilize on every Noetherian module. -/
lemma exists_power_torsion_bound_of_noetherian [IsNoetherian R M] (a : R) :
    ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0 := by
  let K : ℕ →o Submodule R M :=
    { toFun := fun n => (a ^ n • (LinearMap.id : M →ₗ[R] M)).ker
      monotone' := by
        intro m n h x hx
        change a ^ m • x = 0 at hx
        change a ^ n • x = 0
        rw [show a ^ n = a ^ (n - m) * a ^ m by
          rw [← pow_add, Nat.sub_add_cancel h], mul_smul, hx, smul_zero] }
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  refine ⟨N, fun n x hx => ?_⟩
  have hx' : x ∈ K (N + n) := K.monotone (Nat.le_add_left n N) hx
  rw [← hN (N + n) (Nat.le_add_right N n)] at hx'
  exact hx'

/-- Finite modules over Noetherian rings have their own uniform power-torsion
bound; the scalar need not be regular. -/
lemma exists_power_torsion_bound_of_finite [IsNoetherianRing R] [Module.Finite R M]
    (a : R) :
    ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0 :=
  exists_power_torsion_bound_of_noetherian a

/-- Tensoring with a flat module preserves a scalar bound on a kernel in M. -/
lemma smul_eq_zero_tensor_of_flat_of_smul_kernel [Module.Flat R F] (a b : R)
    (h : ∀ x : M, a • x = 0 → b • x = 0)
    (x : M ⊗[R] F) (hx : a • x = 0) : b • x = 0 := by
  let f : M →ₗ[R] M := a • LinearMap.id
  let K := f.ker
  have he : Function.Exact K.subtype f := f.exact_subtype_ker_map
  have ht := Module.Flat.rTensor_exact (M := F) he
  have hz : f.rTensor F x = 0 := by
    simpa [f] using hx
  obtain ⟨z, hz⟩ := (ht x).mp hz
  have hk : ∀ z : K ⊗[R] F, b • K.subtype.rTensor F z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul y v =>
      have hy : b • (y : M) = 0 := h y y.property
      simp [TensorProduct.smul_tmul', hy]
    | add z w hz hw => simp only [map_add, smul_add, hz, hw, add_zero]
  simpa only [hz] using hk z

/-- The same uniform bound passes from a test module to all its flat tensors. -/
lemma flat_tensor_power_torsion_bound [Module.Flat R F] (a : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0) :
    ∀ n : ℕ, ∀ x : M ⊗[R] F, a ^ n • x = 0 → a ^ N • x = 0 :=
  fun n x hx => smul_eq_zero_tensor_of_flat_of_smul_kernel (a ^ n) (a ^ N) (h n) x hx

end SerrePositivity

end ModulePowerTorsionBoundPart

section FiniteTensorCompletePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- Tensoring a complete module with a finite free module preserves completeness,
including rank zero and the zero ring. -/
lemma isModuleComplete_tensor_finite_free (M P : ModuleCat.{u} R)
    [Module.Free R P] [Module.Finite R P] (hM : IsModuleComplete R a M) :
    IsModuleComplete R a ((tensorLeft M).obj P) := by
  classical
  let b := (Module.Free.chooseBasis R P).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex R P))
  let e := TensorProduct.congr (LinearEquiv.refl R M) b.equivFun ≪≫ₗ
    TensorProduct.piScalarRight R R M _
  apply isModuleComplete_of_linearEquiv R a
    (ModuleCat.of R (Fin (Fintype.card (Module.Free.ChooseBasisIndex R P)) → M))
    (ModuleCat.of R (TensorProduct R M P)) e.symm
  exact isModuleComplete_pi R a (fun _ => M) (fun _ => hM)

/-- Reindexing a chain complex to the standard nonpositive cochain degrees
preserves termwise completeness. The added positive-degree terms are zero. -/
lemma isComplete_Q_extend_chain_of_terms
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : ∀ n, IsModuleComplete R a (K.X n)) :
    IsComplete R a (DerivedCategory.Q.obj (K.extend embUp)) := by
  apply isComplete_Q_of_terms R a
  intro i
  by_cases hi : ∃ n, embUp.f n = i
  · obtain ⟨n, rfl⟩ := hi
    exact isModuleComplete_of_linearEquiv R a _ _
      (K.extendXIso embUp rfl).symm.toLinearEquiv (hK n)
  · have hz := HomologicalComplex.isZero_extend_X K embUp i (fun n hn => hi ⟨n, hn⟩)
    let : Subsingleton ((K.extend embUp).X i) := ModuleCat.isZero_iff_subsingleton.mp hz
    exact isModuleComplete_of_pow_smul_zero R a _ 0 (fun _ => Subsingleton.elim _ _)

/-- Any specified resolution with finite free terms makes the original realized
derived tensor complete. The resolution may have infinite length. -/
lemma realizedDerivedTensor_isComplete_of_finite_free_resolution
    (M N : ModuleCat.{u} R) (P : ProjectiveResolution N)
    (hfree : ∀ n, Module.Free R (P.complex.X n))
    (hfinite : ∀ n, Module.Finite R (P.complex.X n))
    (hM : IsModuleComplete R a M) :
    IsComplete R a ((realizedDerivedTensorFunctor R M).obj N) := by
  apply isComplete_of_iso R a (realizedDerivedTensorResolutionIso M P).symm
  apply isComplete_Q_extend_chain_of_terms R a
  intro n
  let := hfree n
  let := hfinite n
  exact isModuleComplete_tensor_finite_free R a M (P.complex.X n) hM

/-- On a regular local base every finitely generated right coefficient has a
finite free resolution, so the actual two-sided derived tensor is complete. -/
lemma boundedAboveDerivedTensor_isComplete_of_finite_regular [IsRegularLocalRing R]
    (M N : ModuleCat.{u} R) [Module.Finite R N] (hM : IsModuleComplete R a M) :
    IsComplete R a ((boundedAboveDerivedTensorModuleFunctor M).obj N) := by
  obtain ⟨rs, hreg, hgen, _⟩ := exists_regular_generators R
  obtain ⟨P, _, hfree, hfinite⟩ :=
    exists_finite_free_resolution_of_regular_generators rs hreg hgen N
  exact isComplete_of_iso R a (boundedAboveDerivedTensorModuleIso M N).symm
    (realizedDerivedTensor_isComplete_of_finite_free_resolution R a M N P hfree hfinite hM)

end SerrePositivity.DerivedCompletion

end FiniteTensorCompletePart

section FiniteCoefficientPowerComparisonPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] [IsRegularLocalRing R] (a : R)
    (C M : ModuleCat.{u} R) [Module.Finite R M]

/-- The actual projective-resolution model with the finite test module unresolved. -/
abbrev finiteCoefficientTensorModel : CochainComplex (ModuleCat.{u} R) ℤ :=
  (moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M

/-- The finite test module's bound is uniform over every term of the original
coefficient resolution, even if that resolution has infinite length. -/
lemma finiteCoefficientTensorModel_has_torsion_bound :
    ∃ N : ℕ, ∀ (i : ℤ) (n : ℕ) (x : (finiteCoefficientTensorModel R C M).X i),
      a ^ n • x = 0 → a ^ N • x = 0 := by
  obtain ⟨N, hN⟩ := exists_power_torsion_bound_of_finite (M := M) a
  refine ⟨N, fun i => ?_⟩
  have : Module.Projective R ((extRes (projectiveResolution C)).X i) := inferInstance
  have : Module.Flat R ((extRes (projectiveResolution C)).X i) := inferInstance
  exact flat_tensor_power_torsion_bound a N hN

/-- The same model represents the complete actual tensor; factor exchange is
the existing signed derived symmetry. -/
lemma finiteCoefficientTensorModel_isComplete (hC : IsModuleComplete R a C) :
    IsComplete R a (DerivedCategory.Q.obj (finiteCoefficientTensorModel R C M)) := by
  let e := (DerivedCategory.Minus.ι (C := ModuleCat.{u} R)).mapIso
    (boundedAboveDerivedTensorSymmetry (boundedAboveDerivedSingleFunctor.obj C)
      (boundedAboveDerivedSingleFunctor.obj M))
  have hc := isComplete_of_iso R a e
    (boundedAboveDerivedTensor_isComplete_of_finite_regular R a C M hC)
  exact isComplete_of_iso R a
    (derivedTensorUnresolvedModuleModelIso M (boundedAboveDerivedSingleFunctor.obj C)
      (projectiveResolutionDerivedModel (projectiveResolution C))) hc

/-- The standard Koszul-to-ordinary-power-cokernel comparison is a genuine
quasi-isomorphism in the model of C ⊗ᴸ M. -/
lemma finiteCoefficientPowerComparison_quasiIso (hC : IsModuleComplete R a C) :
    QuasiIso (koszulPowerCokernelComparison a (finiteCoefficientTensorModel R C M)) := by
  obtain ⟨N, hN⟩ := finiteCoefficientTensorModel_has_torsion_bound R a C M
  exact koszulPowerCokernelComparison_quasiIso_of_term_bound a _ N hN
    (finiteCoefficientTensorModel_isComplete R a C M hC)

end SerrePositivity.DerivedCompletion

end FiniteCoefficientPowerComparisonPart

section FiniteCoefficientPowerHolimPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R) (C M : ModuleCat.{u} R)

/-- A concrete model for the holim of the actual C ⊗ᴸ (M/aⁿM) stages. -/
abbrev modulePowerDerivedTensorHolimComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  complexTowerHomotopyLimit R (modulePowerTensorTower a M (extRes (projectiveResolution C)))
    (modulePowerTensorTransition a M (extRes (projectiveResolution C)))

/-- The original holim projection followed by the actual derived stage comparison. -/
def modulePowerDerivedTensorHolimProjection (n : ℕ) :
    DerivedCategory.Q.obj (modulePowerDerivedTensorHolimComplex R a C M) ⟶
      (boundedAboveDerivedTensorModuleFunctor C).obj (modulePowerReduction a M n) :=
  DerivedCategory.Q.map (complexTowerProjection R
    (modulePowerTensorTower a M (extRes (projectiveResolution C)))
    (modulePowerTensorTransition a M (extRes (projectiveResolution C))) ≫
      Pi.π (modulePowerTensorTower a M (extRes (projectiveResolution C))) n) ≫
        (derivedTensorCoefficientModelIso C (modulePowerReduction a M n)).inv

variable [IsRegularLocalRing R] [Module.Finite R M]

/-- Completeness of C and finiteness of M supply both actual reconstruction inputs. -/
lemma finiteCoefficientPowerReconstruction_quasiIso (hC : IsModuleComplete R a C) :
    QuasiIso (modulePowerTensorReconstruction a M (extRes (projectiveResolution C))) := by
  obtain ⟨N, hN⟩ := finiteCoefficientTensorModel_has_torsion_bound R a C M
  exact modulePowerTensorReconstruction_quasiIso a M (extRes (projectiveResolution C))
    (moduleCoefficientResolution_flat C) N hN
    (finiteCoefficientTensorModel_isComplete R a C M hC)

/-- The same actual C ⊗ᴸ M is the holim of its ordinary test-module quotient stages. -/
def finiteCoefficientPowerHolimIso (hC : IsModuleComplete R a C) :
    (boundedAboveDerivedTensorModuleFunctor C).obj M ≅
      DerivedCategory.Q.obj (modulePowerDerivedTensorHolimComplex R a C M) := by
  have := finiteCoefficientPowerReconstruction_quasiIso R a C M hC
  exact derivedTensorCoefficientModelIso C M ≪≫
    asIso (DerivedCategory.Q.map
      (modulePowerTensorReconstruction a M (extRes (projectiveResolution C))))

/-- Every projection is precisely the original derived quotient map. -/
@[reassoc] lemma finiteCoefficientPowerHolimIso_projection
    (hC : IsModuleComplete R a C) (n : ℕ) :
    (finiteCoefficientPowerHolimIso R a C M hC).hom ≫
      modulePowerDerivedTensorHolimProjection R a C M n =
        (boundedAboveDerivedTensorModuleFunctor C).map (modulePowerReductionMap a M n) := by
  have h := derivedTensorCoefficientModelIso_naturality C (modulePowerReductionMap a M n)
  simp only [finiteCoefficientPowerHolimIso, Iso.trans_hom, asIso_hom,
    modulePowerDerivedTensorHolimProjection, Category.assoc]
  rw [← Category.assoc (DerivedCategory.Q.map _), ← Functor.map_comp,
    modulePowerTensorReconstruction_projection]
  change _ ≫ (DerivedCategory.Q.map
    ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).map
      (modulePowerReductionMap a M n)) ≫ _) = _
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.DerivedCompletion

end FiniteCoefficientPowerHolimPart

section ModulePowerHolimNaturalityPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R) (M : ModuleCat.{u} R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Original quotient transitions commute with every coefficient-complex map. -/
lemma modulePowerTensorTransition_naturality (f : K ⟶ L) (n : ℕ) :
    modulePowerTensorTransition a M K n ≫
        (((tensorLeft (modulePowerReduction a M n)).mapHomologicalComplex (.up ℤ)).map f) =
      (((tensorLeft (modulePowerReduction a M (n + 1))).mapHomologicalComplex (.up ℤ)).map f) ≫
        modulePowerTensorTransition a M L n :=
  (NatTrans.mapHomologicalComplex
    ((tensoringLeft (ModuleCat R)).map (modulePowerReductionTransition a M n)) (.up ℤ)).naturality f |>.symm

/-- The coefficient-complex map induces a map of the same ordinary-quotient holims. -/
def modulePowerTensorHolimMap (f : K ⟶ L) :
    complexTowerHomotopyLimit R (modulePowerTensorTower a M K) (modulePowerTensorTransition a M K) ⟶
      complexTowerHomotopyLimit R (modulePowerTensorTower a M L) (modulePowerTensorTransition a M L) :=
  complexTowerHomotopyLimitMap R (modulePowerTensorTransition a M K)
    (modulePowerTensorTransition a M L)
    (fun n => ((tensorLeft (modulePowerReduction a M n)).mapHomologicalComplex (.up ℤ)).map f)
    (modulePowerTensorTransition_naturality a M f)

/-- Reconstruction intertwines the original coefficient action and its tower action. -/
@[reassoc] lemma modulePowerTensorReconstruction_naturality (f : K ⟶ L) :
    modulePowerTensorReconstruction a M K ≫ modulePowerTensorHolimMap a M f =
      (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map f) ≫
        modulePowerTensorReconstruction a M L := by
  apply complexTowerCompatibleLift_naturality
  intro n
  exact ((NatTrans.mapHomologicalComplex
    ((tensoringLeft (ModuleCat R)).map (modulePowerReductionMap a M n)) (.up ℤ)).naturality f).symm

/-- The actual coefficient morphism, lifted to the original fixed resolutions. -/
def modulePowerDerivedTensorHolimMap {C D : ModuleCat.{u} R} (f : C ⟶ D) :
    DerivedCategory.Q.obj (modulePowerDerivedTensorHolimComplex R a C M) ⟶
      DerivedCategory.Q.obj (modulePowerDerivedTensorHolimComplex R a D M) :=
  DerivedCategory.Q.map (modulePowerTensorHolimMap a M
    (extLift (projectiveResolution C) f (projectiveResolution D)))

/-- The actual derived reconstruction preserves arbitrary coefficient morphisms. -/
@[reassoc] lemma finiteCoefficientPowerHolimIso_naturality_left
    [IsRegularLocalRing R] [Module.Finite R M]
    {C D : ModuleCat.{u} R} (f : C ⟶ D)
    (hC : IsModuleComplete R a C) (hD : IsModuleComplete R a D) :
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map f)
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))).hom ≫
        (finiteCoefficientPowerHolimIso R a D M hD).hom =
      (finiteCoefficientPowerHolimIso R a C M hC).hom ≫
        modulePowerDerivedTensorHolimMap a M f := by
  have hn := derivedTensorCoefficientModelIso_naturality_left M f
  have hr := modulePowerTensorReconstruction_naturality a M
    (extLift (projectiveResolution C) f (projectiveResolution D))
  simp only [finiteCoefficientPowerHolimIso, Iso.trans_hom, asIso_hom,
    modulePowerDerivedTensorHolimMap]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    ← hr, Functor.map_comp, ← Category.assoc]

end SerrePositivity.DerivedCompletion

end ModulePowerHolimNaturalityPart

section ModulePowerTorComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R) (C M : ModuleCat.{u} R)

/-- The homology of the original power cokernel is the standard Tor module,
with C first and the ordinary M/aⁿM as the test module. -/
def modulePowerCokernelTorIso (n i : ℕ) :
    (powerCokernelComplex a
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n).homology
        (-(i : ℤ)) ≅ ((Tor (ModuleCat R) i).obj C).obj (modulePowerReduction a M n) :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-(i : ℤ))).symm.app _ ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))).mapIso
      (modulePowerDerivedTensorIso a C M n) ≪≫
        (boundedAboveDerivedTensorModuleTorNatIso C i).app (modulePowerReduction a M n)

/-- The homology tower uses the standard Tor maps of the ordinary quotient
transitions, in every degree and including the zero-power stage. -/
@[reassoc] lemma modulePowerCokernelTorIso_transition (n i : ℕ) :
    homologyMap (powerCokernelComplexTransition a
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n) (-(i : ℤ)) ≫
        (modulePowerCokernelTorIso a C M n i).hom =
      (modulePowerCokernelTorIso a C M (n + 1) i).hom ≫
        ((Tor (ModuleCat R) i).obj C).map (modulePowerReductionTransition a M n) := by
  let fk := powerCokernelComplexTransition a
    ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n
  let H := DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))
  have h₁ := (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-(i : ℤ))).inv.naturality fk
  have h₂ := congrArg H.map (modulePowerDerivedTensorIso_transition a C M n)
  simp only [Functor.map_comp] at h₂
  have h₃ := (boundedAboveDerivedTensorModuleTorNatIso C i).hom.naturality
    (modulePowerReductionTransition a M n)
  dsimp only [fk, Functor.comp_map] at h₁
  change homologyMap (powerCokernelComplexTransition a
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n) (-(i : ℤ)) ≫ _ =
    _ ≫ H.map (DerivedCategory.Q.map (powerCokernelComplexTransition a
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n)) at h₁
  dsimp only [Functor.comp_map] at h₃
  simp only [modulePowerCokernelTorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, h₁, Category.assoc]
  rw [← Category.assoc (H.map (DerivedCategory.Q.map fk)), h₂]
  simp only [Category.assoc]
  rw [h₃]

variable {C} {D : ModuleCat.{u} R}

@[reassoc] lemma modulePowerCokernelTorIso_naturality (f : C ⟶ D) (n i : ℕ) :
    homologyMap (modulePowerTensorCokernelMap a M
      (extLift (projectiveResolution C) f (projectiveResolution D)) n) (-(i : ℤ)) ≫
        (modulePowerCokernelTorIso a D M n i).hom =
      (modulePowerCokernelTorIso a C M n i).hom ≫
        ((Tor (ModuleCat R) i).map f).app (modulePowerReduction a M n) := by
  let fk := modulePowerTensorCokernelMap a M
    (extLift (projectiveResolution C) f (projectiveResolution D)) n
  let H := DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))
  have h₁ := (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-(i : ℤ))).inv.naturality fk
  have h₂ := congrArg H.map (modulePowerDerivedTensorIso_naturality a M f n)
  simp only [Functor.map_comp] at h₂
  have h₃ := boundedAboveDerivedTensorModuleTorIso_naturality_left f
    (modulePowerReduction a M n) i
  dsimp only [fk, Functor.comp_map] at h₁
  change homologyMap (modulePowerTensorCokernelMap a M
      (extLift (projectiveResolution C) f (projectiveResolution D)) n) (-(i : ℤ)) ≫ _ =
    _ ≫ H.map (DerivedCategory.Q.map (modulePowerTensorCokernelMap a M
      (extLift (projectiveResolution C) f (projectiveResolution D)) n)) at h₁
  simp only [modulePowerCokernelTorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, h₁, Category.assoc]
  rw [← Category.assoc (H.map (DerivedCategory.Q.map fk)), h₂]
  simp only [Category.assoc]
  rw [h₃]

end SerrePositivity.DerivedCompletion

end ModulePowerTorComparisonPart

section FiniteCoefficientCokernelHolimPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (a : R)
    (C M : ModuleCat.{u} R) [Module.Finite R M]

/-- The original power-cokernel reconstruction is a quasi-isomorphism for finite tests. -/
lemma finiteCoefficientPowerCokernelReconstruction_quasiIso (hC : IsModuleComplete R a C) :
    QuasiIso (powerCokernelReconstruction a (finiteCoefficientTensorModel R C M)) := by
  obtain ⟨N, hN⟩ := finiteCoefficientTensorModel_has_torsion_bound R a C M
  exact powerCokernelReconstruction_quasiIso_of_term_bound a _ N hN
    (finiteCoefficientTensorModel_isComplete R a C M hC)

/-- Use the existing actual tensor and the original reconstruction, with no new completion choice. -/
def finiteCoefficientPowerCokernelHolimIso (hC : IsModuleComplete R a C) :
    (boundedAboveDerivedTensorModuleFunctor C).obj M ≅
      DerivedCategory.Q.obj (complexTowerHomotopyLimit R
        (powerCokernelComplex a (finiteCoefficientTensorModel R C M))
        (powerCokernelComplexTransition a (finiteCoefficientTensorModel R C M))) := by
  have := finiteCoefficientPowerCokernelReconstruction_quasiIso a C M hC
  exact derivedTensorCoefficientModelIso C M ≪≫
    asIso (DerivedCategory.Q.map (powerCokernelReconstruction a (finiteCoefficientTensorModel R C M)))

/-- Naturality uses the original lift of the coefficient morphism. -/
@[reassoc] lemma finiteCoefficientPowerCokernelHolimIso_naturality_left
    {D : ModuleCat.{u} R} (f : C ⟶ D)
    (hC : IsModuleComplete R a C) (hD : IsModuleComplete R a D) :
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map f)
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))).hom ≫
        (finiteCoefficientPowerCokernelHolimIso a D M hD).hom =
      (finiteCoefficientPowerCokernelHolimIso a C M hC).hom ≫
        DerivedCategory.Q.map (powerCokernelHolimMap a
          (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
            (extLift (projectiveResolution C) f (projectiveResolution D)))) := by
  have hn := derivedTensorCoefficientModelIso_naturality_left M f
  have hr := powerCokernelReconstruction_naturality a
    (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
      (extLift (projectiveResolution C) f (projectiveResolution D)))
  change powerCokernelReconstruction a (finiteCoefficientTensorModel R C M) ≫
      powerCokernelHolimMap a (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
        (extLift (projectiveResolution C) f (projectiveResolution D))) =
    (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
      (extLift (projectiveResolution C) f (projectiveResolution D))) ≫
        powerCokernelReconstruction a (finiteCoefficientTensorModel R D M) at hr
  simp only [finiteCoefficientPowerCokernelHolimIso, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    ← hr, Functor.map_comp, ← Category.assoc]

end SerrePositivity.DerivedCompletion

end FiniteCoefficientCokernelHolimPart
