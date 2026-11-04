module

public import SerrePositivity.HomologicalAlgebra.TorAlgebraNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleTower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Milnor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTower
public import SerrePositivity.HomologicalAlgebra.AlgebraEquivariantShortComplex
public import SerrePositivity.HomologicalAlgebra.TorAlgebraScalarComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Reconstruction

/-! # 有限な試験加群の Tor の導来完備性

## 概要

通常の冪商の Tor の塔を係数代数上の加群の塔として扱い、その lim と lim¹ が完備であること、二つの端点上のイデアルの作用、冪の余核の Milnor 列の端点・中央と代数値の Tor との比較を与え、有限な試験加群の Tor 加群が係数代数上で導来完備であること（`TorAlgebraComplete`）を示す。

## 方針

代数値の左導来関手の段と遷移をそのまま使い、Milnor 列の両端と中央を代数の加群として比べる。段の零化は条件として受け取り、イデアルの冪等性は仮定しない。

## 規約

どちらの端点も捨てない。

## 使われ方

CLMST の almost な Tor の比較と完備性。
-/

@[expose] public noncomputable section

universe u

section ModulePowerTorAlgebraTowerPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable {R : Type u} [CommRing R] (a : R)
    (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R) (i : ℕ)

abbrev modulePowerTorAlgebraTower (n : ℕ) : ModuleCat.{u} C :=
  ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj (modulePowerReduction a M n)

def modulePowerTorAlgebraTransition (n : ℕ) :
    modulePowerTorAlgebraTower a C M i (n + 1) ⟶ modulePowerTorAlgebraTower a C M i n :=
  ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).map (modulePowerReductionTransition a M n)

lemma modulePowerTorAlgebra_pow_smul_zero (n : ℕ) (x : modulePowerTorAlgebraTower a C M i n) :
    (algebraMap R C a) ^ n • x = 0 := by
  simpa only [map_pow] using torAlg_smul_eq_zero (algebraMap R C) i
    (modulePowerReduction a M n) (a ^ n) (modulePowerReduction_pow_smul_zero a M n) x

lemma modulePowerTorAlgebra_isModuleComplete (n : ℕ) :
    IsModuleComplete C (algebraMap R C a) (modulePowerTorAlgebraTower a C M i n) :=
  isModuleComplete_of_pow_smul_zero C (algebraMap R C a) _ n
    (modulePowerTorAlgebra_pow_smul_zero a C M i n)

abbrev modulePowerTorAlgebraLimit : ModuleCat.{u} C :=
  ModuleCat.of C (moduleTowerLimit C (fun n => modulePowerTorAlgebraTower a C M i n)
    (fun n => (modulePowerTorAlgebraTransition a C M i n).hom))

abbrev modulePowerTorAlgebraLimOne : ModuleCat.{u} C :=
  ModuleCat.of C ((∀ n, modulePowerTorAlgebraTower a C M i n) ⧸
    (moduleTowerDifference C (fun n => modulePowerTorAlgebraTower a C M i n)
      (fun n => (modulePowerTorAlgebraTransition a C M i n).hom)).range)

lemma modulePowerTorAlgebraLimit_isModuleComplete :
    IsModuleComplete C (algebraMap R C a) (modulePowerTorAlgebraLimit a C M i) := by
  have hp := isModuleComplete_pi C (algebraMap R C a)
    (modulePowerTorAlgebraTower a C M i) (modulePowerTorAlgebra_isModuleComplete a C M i)
  exact isModuleComplete_ker C (algebraMap R C a)
    (M := ModuleCat.of C (∀ n, modulePowerTorAlgebraTower a C M i n))
    (N := ModuleCat.of C (∀ n, modulePowerTorAlgebraTower a C M i n)) _ hp hp

lemma modulePowerTorAlgebraLimOne_isModuleComplete :
    IsModuleComplete C (algebraMap R C a) (modulePowerTorAlgebraLimOne a C M i) := by
  have hp := isModuleComplete_pi C (algebraMap R C a)
    (modulePowerTorAlgebraTower a C M i) (modulePowerTorAlgebra_isModuleComplete a C M i)
  exact isModuleComplete_coker C (algebraMap R C a)
    (M := ModuleCat.of C (∀ n, modulePowerTorAlgebraTower a C M i n))
    (N := ModuleCat.of C (∀ n, modulePowerTorAlgebraTower a C M i n)) _ hp hp

/-- Standard Tor transitions become exactly the actual C-linear quotient transitions. -/
@[reassoc] lemma modulePowerTorAlgebraComparison_transition (n : ℕ) :
    ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).map (modulePowerReductionTransition a M n) ≫
        (torAlgebraComparison (C := C) (modulePowerReduction a M n) i).hom =
      (torAlgebraComparison (C := C) (modulePowerReduction a M (n + 1)) i).hom ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map
          (modulePowerTorAlgebraTransition a C M i n) :=
  torAlgebraComparison_naturality (modulePowerReductionTransition a M n) i

end SerrePositivity.DerivedCompletion

end ModulePowerTorAlgebraTowerPart

section ModulePowerTorAlgebraAlmostPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable {R : Type u} [CommRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R) (i : ℕ)
  (B : Type u) [CommRing B] (ψ : B →+* C) (I : Ideal B)
  (hTor : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
    (∀ x : N, a ^ k • x = 0) → ∀ b ∈ I, torCoefficientScalarEndomorphism C N i (ψ b) = 0)

include hTor in
lemma modulePowerTorAlgebraStage_annihilated (n : ℕ) :
    I ≤ Module.annihilator B ((ModuleCat.restrictScalars ψ).obj
      (modulePowerTorAlgebraTower a C M i n)) := by
  intro b hb
  rw [Module.mem_annihilator]
  have ht : ∀ x : modulePowerReduction a M n, a ^ (n + 1) • x = 0 := by
    intro x
    rw [pow_succ', mul_smul, modulePowerReduction_pow_smul_zero, smul_zero]
  exact (torAlgebraComparison_scalar_zero_iff_forall (modulePowerReduction a M n) i (ψ b)).mp
    (hTor _ (n + 1) (Nat.succ_pos _) ht b hb)

include hTor in
lemma modulePowerTorAlgebraLimit_annihilated :
    I ≤ Module.annihilator B ((ModuleCat.restrictScalars ψ).obj
      (modulePowerTorAlgebraLimit a C M i)) := by
  intro b hb
  rw [Module.mem_annihilator]
  intro x
  apply Subtype.ext
  funext n
  exact Module.mem_annihilator.mp
    (modulePowerTorAlgebraStage_annihilated a C M i B ψ I hTor n hb) (x.val n)

include hTor in
lemma modulePowerTorAlgebraLimOne_annihilated :
    I ≤ Module.annihilator B ((ModuleCat.restrictScalars ψ).obj
      (modulePowerTorAlgebraLimOne a C M i)) := by
  intro b hb
  rw [Module.mem_annihilator]
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    change Submodule.Quotient.mk ((ψ b) • y) = 0
    have hy : (ψ b) • y = 0 := by
      funext n
      exact Module.mem_annihilator.mp
        (modulePowerTorAlgebraStage_annihilated a C M i B ψ I hTor n hb) (y n)
    rw [hy]
    rfl

/-- The limit endpoint is complete over any original coefficient source B→C. -/
lemma modulePowerTorAlgebraLimit_isModuleComplete_restrict (p : ℕ) :
    IsModuleComplete B (p : B) ((ModuleCat.restrictScalars ψ).obj
      (modulePowerTorAlgebraLimit (p : R) C M i)) := by
  letI : Algebra B C := ψ.toAlgebra
  let X := modulePowerTorAlgebraLimit (p : R) C M i
  letI : Module B X := Module.compHom X ψ
  letI : IsScalarTower B C X := IsScalarTower.of_algebraMap_smul fun r x => rfl
  have hc : IsModuleComplete C (algebraMap B C (p : B)) X := by
    simpa only [map_natCast] using modulePowerTorAlgebraLimit_isModuleComplete (p : R) C M i
  exact (isModuleComplete_algebraMap_iff B C (p : B) X).mp hc

/-- The lim¹ endpoint is complete as well, without a surjectivity or vanishing hypothesis. -/
lemma modulePowerTorAlgebraLimOne_isModuleComplete_restrict (p : ℕ) :
    IsModuleComplete B (p : B) ((ModuleCat.restrictScalars ψ).obj
      (modulePowerTorAlgebraLimOne (p : R) C M i)) := by
  letI : Algebra B C := ψ.toAlgebra
  let X := modulePowerTorAlgebraLimOne (p : R) C M i
  letI : Module B X := Module.compHom X ψ
  letI : IsScalarTower B C X := IsScalarTower.of_algebraMap_smul fun r x => rfl
  have hc : IsModuleComplete C (algebraMap B C (p : B)) X := by
    simpa only [map_natCast] using modulePowerTorAlgebraLimOne_isModuleComplete (p : R) C M i
  exact (isModuleComplete_algebraMap_iff B C (p : B) X).mp hc

end SerrePositivity.DerivedCompletion

end ModulePowerTorAlgebraAlmostPart

section ModulePowerTorAlgebraMilnorPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R)
local notation "K₀" => CategoryTheory.Functor.obj (moduleTensorCochainFunctor
  (extRes (projectiveResolution (ModuleCat.of R C)))) M

/-- The same power-cokernel homology, now with the actual coefficient-algebra target. -/
def modulePowerCokernelTorAlgebraIso (n i : ℕ) :
    (powerCokernelComplex a K₀ n).homology (-(i : ℤ)) ≅
      (ModuleCat.restrictScalars (algebraMap R C)).obj (modulePowerTorAlgebraTower a C M i n) :=
  modulePowerCokernelTorIso a (ModuleCat.of R C) M n i ≪≫
    torAlgebraComparison (modulePowerReduction a M n) i

@[reassoc] lemma modulePowerCokernelTorAlgebraIso_transition (n i : ℕ) :
    HomologicalComplex.homologyMap (powerCokernelComplexTransition a K₀ n) (-(i : ℤ)) ≫
        (modulePowerCokernelTorAlgebraIso a C M n i).hom =
      (modulePowerCokernelTorAlgebraIso a C M (n + 1) i).hom ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map
          (modulePowerTorAlgebraTransition a C M i n) := by
  simp only [modulePowerCokernelTorAlgebraIso, Iso.trans_hom]
  rw [← Category.assoc, modulePowerCokernelTorIso_transition, Category.assoc,
    modulePowerTorAlgebraComparison_transition]
  simp only [Category.assoc]

@[reassoc] lemma modulePowerCokernelTorAlgebraIso_scalar (n i : ℕ) (c : C) :
    HomologicalComplex.homologyMap (modulePowerTensorCokernelMap a M
      (extLift (projectiveResolution (ModuleCat.of R C))
        (ModuleCat.ofHom (LinearMap.mulLeft R c)) (projectiveResolution (ModuleCat.of R C))) n)
      (-(i : ℤ)) ≫ (modulePowerCokernelTorAlgebraIso a C M n i).hom =
        (modulePowerCokernelTorAlgebraIso a C M n i).hom ≫
          (ModuleCat.restrictScalars (algebraMap R C)).map
            (c • 𝟙 (modulePowerTorAlgebraTower a C M i n)) := by
  have ht := modulePowerCokernelTorIso_naturality a M
    (ModuleCat.ofHom (LinearMap.mulLeft R c)) n i
  change _ ≫ (modulePowerCokernelTorIso a (ModuleCat.of R C) M n i).hom =
    (modulePowerCokernelTorIso a (ModuleCat.of R C) M n i).hom ≫
      torCoefficientScalarEndomorphism C (modulePowerReduction a M n) i c at ht
  simp only [modulePowerCokernelTorAlgebraIso, Iso.trans_hom]
  rw [reassoc_of% ht, torAlgebraComparison_coefficient_scalar]
  simp only [Category.assoc]

/-- The actual kernel term of the original power-cokernel Milnor sequence. -/
def modulePowerCokernelTorAlgebraLimitComparison (i : ℕ) :
    moduleTowerLimit R (fun n => (powerCokernelComplex a K₀ n).homology (-(i : ℤ)))
      (fun n => (HomologicalComplex.homologyMap
        (powerCokernelComplexTransition a K₀ n) (-(i : ℤ))).hom) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R C)).obj (modulePowerTorAlgebraLimit a C M i) :=
  (moduleTowerLimitEquiv R
    (M := fun n => (powerCokernelComplex a K₀ n).homology (-(i : ℤ)))
    (N := fun n => (ModuleCat.restrictScalars (algebraMap R C)).obj
      (modulePowerTorAlgebraTower a C M i n))
    (fun n => (HomologicalComplex.homologyMap
      (powerCokernelComplexTransition a K₀ n) (-(i : ℤ))).hom)
    (fun n => ((ModuleCat.restrictScalars (algebraMap R C)).map
      (modulePowerTorAlgebraTransition a C M i n)).hom)
    (fun n => (modulePowerCokernelTorAlgebraIso a C M n i).toLinearEquiv)
    (fun n x => congrArg (fun f => f.hom x)
      (modulePowerCokernelTorAlgebraIso_transition a C M n i))).trans
        (moduleTowerLimitRestrictScalarsEquiv R
          (modulePowerTorAlgebraTower a C M i) (modulePowerTorAlgebraTransition a C M i))

/-- The actual cokernel term of the original power-cokernel Milnor sequence. -/
def modulePowerCokernelTorAlgebraLimOneComparison (i : ℕ) :
    complexTowerHomologyLimOne R (powerCokernelComplex a K₀)
      (powerCokernelComplexTransition a K₀) (-(i : ℤ)) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R C)).obj (modulePowerTorAlgebraLimOne a C M i) :=
  (moduleTowerLimOneEquiv R
    (M := fun n => (powerCokernelComplex a K₀ n).homology (-(i : ℤ)))
    (N := fun n => (ModuleCat.restrictScalars (algebraMap R C)).obj
      (modulePowerTorAlgebraTower a C M i n))
    (fun n => (HomologicalComplex.homologyMap
      (powerCokernelComplexTransition a K₀ n) (-(i : ℤ))).hom)
    (fun n => ((ModuleCat.restrictScalars (algebraMap R C)).map
      (modulePowerTorAlgebraTransition a C M i n)).hom)
    (fun n => (modulePowerCokernelTorAlgebraIso a C M n i).toLinearEquiv)
    (fun n x => congrArg (fun f => f.hom x)
      (modulePowerCokernelTorAlgebraIso_transition a C M n i))).trans
        (moduleTowerLimOneRestrictScalarsEquiv R
          (modulePowerTorAlgebraTower a C M i) (modulePowerTorAlgebraTransition a C M i))

@[simp] lemma modulePowerCokernelTorAlgebraLimitComparison_apply (i : ℕ)
    (x : moduleTowerLimit R (fun n => (powerCokernelComplex a K₀ n).homology (-(i : ℤ)))
      (fun n => (HomologicalComplex.homologyMap
        (powerCokernelComplexTransition a K₀ n) (-(i : ℤ))).hom)) (n : ℕ) :
    (modulePowerCokernelTorAlgebraLimitComparison a C M i x).val n =
      (modulePowerCokernelTorAlgebraIso a C M n i).hom (x.val n) := rfl

@[simp] lemma modulePowerCokernelTorAlgebraLimOneComparison_mk (i : ℕ)
    (x : ∀ n, (powerCokernelComplex a K₀ n).homology (-(i : ℤ))) :
    modulePowerCokernelTorAlgebraLimOneComparison a C M i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (fun n => (modulePowerCokernelTorAlgebraIso a C M n i).hom (x n)) := rfl

end SerrePositivity.DerivedCompletion

end ModulePowerTorAlgebraMilnorPart

section TorAlgebraMilnorActionsPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
variable {R : Type u} [CommRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R)
local notation "K₀" => CategoryTheory.Functor.obj (moduleTensorCochainFunctor
  (extRes (projectiveResolution (ModuleCat.of R C)))) M

/-- The original lift of coefficient multiplication in the unresolved-test tensor model. -/
abbrev modulePowerCoefficientLift (c : C) : K₀ ⟶ K₀ :=
  ((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
    (extLift (projectiveResolution (ModuleCat.of R C)) (ModuleCat.ofHom (LinearMap.mulLeft R c))
      (projectiveResolution (ModuleCat.of R C)))

/-- The original induced endomorphism of the original Milnor short complex. -/
def modulePowerCokernelMilnorScalarMap (c : C) (j : ℤ) :
    complexTowerMilnorSequence R (powerCokernelComplex a K₀)
      (powerCokernelComplexTransition a K₀) j ⟶
    complexTowerMilnorSequence R (powerCokernelComplex a K₀)
      (powerCokernelComplexTransition a K₀) j :=
  complexTowerMilnorSequenceMap R _ _
    (powerCokernelMap a (modulePowerCoefficientLift C M c))
    (powerCokernelMap_transition a (modulePowerCoefficientLift C M c)) j

lemma modulePowerCokernelTorAlgebraLimitComparison_scalar (i : ℕ) (c : C)
    (x : moduleTowerLimit R (fun n => (powerCokernelComplex a K₀ n).homology (-(i : ℤ)))
      (fun n => (HomologicalComplex.homologyMap
        (powerCokernelComplexTransition a K₀ n) (-(i : ℤ))).hom)) :
    modulePowerCokernelTorAlgebraLimitComparison a C M i
      (complexTowerHomologyLimitMap R _ _
        (powerCokernelMap a (modulePowerCoefficientLift C M c))
        (powerCokernelMap_transition a (modulePowerCoefficientLift C M c)) (-(i : ℤ)) x) =
      (ModuleCat.restrictScalars (algebraMap R C)).map
        (c • 𝟙 (modulePowerTorAlgebraLimit a C M i))
        (modulePowerCokernelTorAlgebraLimitComparison a C M i x) := by
  apply Subtype.ext
  funext n
  rw [modulePowerCokernelTorAlgebraLimitComparison_apply]
  change (modulePowerCokernelTorAlgebraIso a C M n i).hom
      (HomologicalComplex.homologyMap (modulePowerTensorCokernelMap a M
        (extLift (projectiveResolution (ModuleCat.of R C))
          (ModuleCat.ofHom (LinearMap.mulLeft R c)) (projectiveResolution (ModuleCat.of R C))) n)
        (-(i : ℤ)) (x.val n)) = _
  exact congrArg (fun f => f.hom (x.val n)) (modulePowerCokernelTorAlgebraIso_scalar a C M n i c)

lemma modulePowerCokernelTorAlgebraLimOneComparison_scalar (i : ℕ) (c : C)
    (x : complexTowerHomologyLimOne R (powerCokernelComplex a K₀)
      (powerCokernelComplexTransition a K₀) (-(i : ℤ))) :
    modulePowerCokernelTorAlgebraLimOneComparison a C M i
      (complexTowerHomologyLimOneMap R _ _
        (powerCokernelMap a (modulePowerCoefficientLift C M c))
        (powerCokernelMap_transition a (modulePowerCoefficientLift C M c)) (-(i : ℤ)) x) =
      (ModuleCat.restrictScalars (algebraMap R C)).map
        (c • 𝟙 (modulePowerTorAlgebraLimOne a C M i))
        (modulePowerCokernelTorAlgebraLimOneComparison a C M i x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    change modulePowerCokernelTorAlgebraLimOneComparison a C M i
      (Submodule.Quotient.mk (fun n => HomologicalComplex.homologyMap
        (powerCokernelMap a (modulePowerCoefficientLift C M c) n) (-(i : ℤ)) (y n))) = _
    rw [modulePowerCokernelTorAlgebraLimOneComparison_mk,
      modulePowerCokernelTorAlgebraLimOneComparison_mk]
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk
      (c • (fun n => (modulePowerCokernelTorAlgebraIso a C M n i).hom (y n)))
    congr 1
    funext n
    exact congrArg (fun f => f.hom (y n)) (modulePowerCokernelTorAlgebraIso_scalar a C M n i c)

/-- Reindex the original lim¹ endpoint by an explicit cochain/Tor degree equality. -/
def modulePowerCokernelTorAlgebraLimOneIsoAt (j : ℤ) (i : ℕ) (hj : j = -(i : ℤ)) :
    ModuleCat.of R (complexTowerHomologyLimOne R (powerCokernelComplex a K₀)
      (powerCokernelComplexTransition a K₀) j) ≅
      (ModuleCat.restrictScalars (algebraMap R C)).obj (modulePowerTorAlgebraLimOne a C M i) := by
  subst j
  exact (modulePowerCokernelTorAlgebraLimOneComparison a C M i).toModuleIso

@[reassoc] lemma modulePowerCokernelTorAlgebraLimOneIsoAt_scalar
    (j : ℤ) (i : ℕ) (hj : j = -(i : ℤ)) (c : C) :
    ModuleCat.ofHom (complexTowerHomologyLimOneMap R _ _
      (powerCokernelMap a (modulePowerCoefficientLift C M c))
      (powerCokernelMap_transition a (modulePowerCoefficientLift C M c)) j) ≫
        (modulePowerCokernelTorAlgebraLimOneIsoAt a C M j i hj).hom =
      (modulePowerCokernelTorAlgebraLimOneIsoAt a C M j i hj).hom ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map
          (c • 𝟙 (modulePowerTorAlgebraLimOne a C M i)) := by
  subst j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact modulePowerCokernelTorAlgebraLimOneComparison_scalar a C M i c x

end SerrePositivity.DerivedCompletion

end TorAlgebraMilnorActionsPart

section TorAlgebraMilnorMiddlePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R) [Module.Finite R M]
local notation "C₀" => ModuleCat.of R C
local notation "K₀" => finiteCoefficientTensorModel R C₀ M
local notation "L₀" => complexTowerHomotopyLimit R (powerCokernelComplex a K₀)
  (powerCokernelComplexTransition a K₀)

/-- The actual middle cohomology of the original Milnor sequence, compared to
algebra-valued Tor through the original reconstruction. -/
def torAlgebraMilnorMiddleIso (hC : IsModuleComplete R a C₀) (i : ℕ) :
    (L₀).homology (-(i : ℤ)) ≅ (ModuleCat.restrictScalars (algebraMap R C)).obj
      (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M) :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-(i : ℤ))).symm.app L₀ ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))).mapIso
      (finiteCoefficientPowerCokernelHolimIso a C₀ M hC).symm ≪≫
        (boundedAboveDerivedTensorModuleTorNatIso C₀ i).app M ≪≫ torAlgebraComparison M i

/-- The original lifted coefficient multiplication on holim becomes exactly the
scalar action on the actual C-module Tor. -/
@[reassoc] lemma torAlgebraMilnorMiddleIso_scalar
    (hC : IsModuleComplete R a C₀) (i : ℕ) (c : C) :
    HomologicalComplex.homologyMap (powerCokernelHolimMap a
      (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
        (extLift (projectiveResolution C₀) (ModuleCat.ofHom (LinearMap.mulLeft R c))
          (projectiveResolution C₀)))) (-(i : ℤ)) ≫
        (torAlgebraMilnorMiddleIso a C M hC i).hom =
      (torAlgebraMilnorMiddleIso a C M hC i).hom ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map
          (c • 𝟙 (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))
  let f : C₀ ⟶ C₀ := ModuleCat.ofHom (LinearMap.mulLeft R c)
  let k := powerCokernelHolimMap a (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
    (extLift (projectiveResolution C₀) f (projectiveResolution C₀)))
  let d := (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
    (boundedAboveDerivedSingleFunctor.map f) (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))).hom
  let e := finiteCoefficientPowerCokernelHolimIso a C₀ M hC
  let q := (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-(i : ℤ))).symm.app L₀
  let t := (boundedAboveDerivedTensorModuleTorNatIso C₀ i).app M
  let b := torAlgebraComparison (C := C) M i
  have hn : d ≫ e.hom = e.hom ≫ DerivedCategory.Q.map k :=
    finiteCoefficientPowerCokernelHolimIso_naturality_left a C₀ M f hC hC
  have hni : DerivedCategory.Q.map k ≫ e.inv = e.inv ≫ d := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  have h₂ := congrArg H.map hni
  simp only [Functor.map_comp] at h₂
  have h₁ := (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-(i : ℤ))).inv.naturality k
  change HomologicalComplex.homologyMap k (-(i : ℤ)) ≫ q.hom =
    q.hom ≫ H.map (DerivedCategory.Q.map k) at h₁
  have h₃ := boundedAboveDerivedTensorModuleTorIso_naturality_left f M i
  change H.map d ≫ t.hom = t.hom ≫ torCoefficientScalarEndomorphism C M i c at h₃
  have h₄ := torAlgebraComparison_coefficient_scalar M i c
  change HomologicalComplex.homologyMap k (-(i : ℤ)) ≫
    (q.hom ≫ H.map e.inv ≫ t.hom ≫ b.hom) =
      (q.hom ≫ H.map e.inv ≫ t.hom ≫ b.hom) ≫ _
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simp only [Category.assoc]
  rfl

end SerrePositivity.DerivedCompletion

end TorAlgebraMilnorMiddlePart

section TorAlgebraMilnorSequencePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R) [Module.Finite R M]
local notation "C₀" => ModuleCat.of R C
local notation "K₀" => finiteCoefficientTensorModel R C₀ M
local notation "S₀" => complexTowerMilnorSequence R (powerCokernelComplex a K₀)
  (powerCokernelComplexTransition a K₀)

/-- lim¹ Tor_(i+1) → Tor_i(C,M) → lim Tor_i, with actual C-linear maps. -/
def torAlgebraMilnorShortComplex (hC : IsModuleComplete R a C₀) (i : ℕ) :
    ShortComplex (ModuleCat.{u} C) := by
  let S := S₀ (-(i : ℤ))
  let X := modulePowerTorAlgebraLimOne a C M (i + 1)
  let Y := ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M
  let Z := modulePowerTorAlgebraLimit a C M i
  have hi : -(i : ℤ) - 1 = -((i + 1 : ℕ) : ℤ) := by omega
  let e₁ : S.X₁ ≅ (ModuleCat.restrictScalars (algebraMap R C)).obj X :=
    modulePowerCokernelTorAlgebraLimOneIsoAt a C M (-(i : ℤ) - 1) (i + 1) hi
  let e₂ : S.X₂ ≅ (ModuleCat.restrictScalars (algebraMap R C)).obj Y :=
    torAlgebraMilnorMiddleIso a C M hC i
  let e₃ : S.X₃ ≅ (ModuleCat.restrictScalars (algebraMap R C)).obj Z :=
    (modulePowerCokernelTorAlgebraLimitComparison a C M i).toModuleIso
  let α : C → (S ⟶ S) := fun c => modulePowerCokernelMilnorScalarMap a C M c (-(i : ℤ))
  refine algebraEquivariantShortComplex S X Y Z e₁ e₂ e₃ α ?_ ?_ ?_
  · intro c
    exact modulePowerCokernelTorAlgebraLimOneIsoAt_scalar a C M (-(i : ℤ) - 1) (i + 1) hi c
  · intro c
    exact torAlgebraMilnorMiddleIso_scalar a C M hC i c
  · intro c
    ext x
    exact modulePowerCokernelTorAlgebraLimitComparison_scalar a C M i c x

lemma torAlgebraMilnorShortComplex_shortExact (hC : IsModuleComplete R a C₀) (i : ℕ) :
    (torAlgebraMilnorShortComplex a C M hC i).ShortExact := by
  dsimp only [torAlgebraMilnorShortComplex]
  apply algebraEquivariantShortComplex_shortExact
  exact complexTowerMilnorSequence_shortExact R _ _ (-(i : ℤ))

/-- The same sequence over an arbitrary original coefficient source B→C. -/
def torAlgebraMilnorShortComplexOver (hC : IsModuleComplete R a C₀) (i : ℕ)
    (B : Type u) [CommRing B] (ψ : B →+* C) : ShortComplex (ModuleCat.{u} B) :=
  (torAlgebraMilnorShortComplex a C M hC i).map (ModuleCat.restrictScalars ψ)

lemma torAlgebraMilnorShortComplexOver_shortExact (hC : IsModuleComplete R a C₀) (i : ℕ)
    (B : Type u) [CommRing B] (ψ : B →+* C) :
    (torAlgebraMilnorShortComplexOver a C M hC i B ψ).ShortExact :=
  (torAlgebraMilnorShortComplex_shortExact a C M hC i).map_of_exact (ModuleCat.restrictScalars ψ)

end SerrePositivity.DerivedCompletion

end TorAlgebraMilnorSequencePart

section TorAlgebraCompletePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C]
  (M : ModuleCat.{u} R) [Module.Finite R M]

/-- Completeness of the actual tensor supplies completeness of the existing standard Tor. -/
lemma torModule_isModuleComplete_of_finite (hC : IsModuleComplete R a (ModuleCat.of R C))
    (i : ℕ) : IsModuleComplete R a
      (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj M) := by
  have hc := boundedAboveDerivedTensor_isComplete_of_finite_regular R a (ModuleCat.of R C) M hC
  have hh := isComplete_homology_isModuleComplete R a _ hc (-(i : ℤ))
  exact isModuleComplete_of_linearEquiv R a _ _
    ((boundedAboveDerivedTensorModuleTorNatIso (ModuleCat.of R C) i).app M).toLinearEquiv hh

/-- The algebra-valued Tor is complete after restriction along the original base action. -/
lemma restrictedTorAlgebra_isModuleComplete_of_finite
    (hC : IsModuleComplete R a (ModuleCat.of R C)) (i : ℕ) :
    IsModuleComplete R a ((ModuleCat.restrictScalars (algebraMap R C)).obj
      (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M)) :=
  isModuleComplete_of_linearEquiv R a _ _ (torAlgebraComparison (C := C) M i).toLinearEquiv
    (torModule_isModuleComplete_of_finite a C M hC i)

/-- In its actual C-module structure, finite-test Tor is derived complete for the image of a. -/
lemma torAlgebra_isModuleComplete_of_finite
    (hC : IsModuleComplete R a (ModuleCat.of R C)) (i : ℕ) :
    IsModuleComplete C (algebraMap R C a)
      (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M) := by
  let X := ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M
  letI : Module R X := Module.compHom X (algebraMap R C)
  letI : IsScalarTower R C X := IsScalarTower.of_algebraMap_smul fun r x => rfl
  exact (isModuleComplete_algebraMap_iff R C a X).mpr
    (restrictedTorAlgebra_isModuleComplete_of_finite a C M hC i)

/-- For a natural-number parameter, completeness also holds over any original
coefficient source B→C; no finiteness hypothesis on B or C is imposed. -/
lemma torAlgebra_isModuleComplete_restrict_of_finite
    (B : Type u) [CommRing B] (ψ : B →+* C) (p : ℕ)
    (hC : IsModuleComplete R (p : R) (ModuleCat.of R C)) (i : ℕ) :
    IsModuleComplete B (p : B) ((ModuleCat.restrictScalars ψ).obj
      (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M)) := by
  letI : Algebra B C := ψ.toAlgebra
  let X := ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M
  letI : Module B X := Module.compHom X ψ
  letI : IsScalarTower B C X := IsScalarTower.of_algebraMap_smul fun r x => rfl
  have hc : IsModuleComplete C (algebraMap B C (p : B)) X := by
    simpa only [map_natCast] using torAlgebra_isModuleComplete_of_finite (p : R) C M hC i
  exact (isModuleComplete_algebraMap_iff B C (p : B) X).mp hc

end SerrePositivity.DerivedCompletion

end TorAlgebraCompletePart
