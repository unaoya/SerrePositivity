module

public import SerrePositivity.BhattScholze.Andre.Envelope.FamilyEvaluation
public import SerrePositivity.BhattScholze.Andre.Envelope.SourceEvaluation
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import Mathlib.RingTheory.TensorProduct.Maps
public import SerrePositivity.BhattScholze.Andre.Envelope.PDivision
public import SerrePositivity.HomologicalAlgebra.DerivedTensorSymmetry
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison
public import SerrePositivity.BhattScholze.Delta.Division.Basic

/-!
# 自由 δ 射に沿う p 除算包のテンソルと導来比較

## 概要
全源評価環への Tor の移送、自由 δ 射の通常テンソル積と raw δ 包・分冪表示環、導来分冪比較、テンソルの δ 構造・p 正則性・導来完備化 H⁰ との比較。

## 方針
主定理には使われない。旧 B4 経路の部品のうち、BS 著者版 Corollary 2.39・BS 著者版 Corollary 2.44 の一般化に使える部分として残した（BS-W8）。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
BS の中には import 元がない（残した結果。`scripts/audit/bhatt_scholze.lean` が監査する）。
-/

universe u

/-! ## G7の交換入力に相対的な全源評価環へのTor移送

標準MathlibのPreservesColimitを明示的に受け取る。
この入力自体を証明したり、G7を受領したりしたという主張ではない。
-/

@[expose] public noncomputable section DeltaPDivisionSourceColimitTor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D (p : A)
local notation "F₀" => deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y

/-- G7の標準colimit交換入力があれば、全源評価環Aの正次数Torが零。
PreservesColimitの入力は未解消の共通基盤への要求として明示している。 -/
theorem deltaPDivisionSource_tor_subsingleton_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (i : ℕ)
    (hpres : PreservesColimit F₀ ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    Subsingleton (SerrePositivity.TorAlg α₀ (i + 1) A) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  exact deltaDivisionEvaluationSource_tor_subsingleton_of_preservesColimit
    D (fun _ : σ => D.frobeniusLift y) α₀ i
    (fun N => deltaPDivisionSourceFinite_tor_subsingleton D y hpA hg v hv hy N i) hpres

end SerrePositivity.BhattScholze

end DeltaPDivisionSourceColimitTor

/-! ## 実自由δ射の通常テンソル積とraw δ包

源Pと終域Lは同じ underlying 型だが、LのP代数構造はα:x↦p zによるもの。
通常テンソル積の標準写像を保つ比較を構成し、導来テンソルの離散性とは区別する。
-/

@[expose] public noncomputable section DeltaPDivisionSourceTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D (p : A)
local notation "β₀" => deltaDivisionSourceEval D a₀
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "q₀" => Ideal.Quotient.mk
  (DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
    (deltaDivisionRelationIdeal (p : A) a₀))

/-- 終域Lの源P代数構造は、実自由δ射αで与える。 -/
@[instance_reducible] def deltaPDivisionSourceTargetAlgebra : Algebra P₀ P₀ :=
  deltaDivisionSourceTargetAlgebra (σ := σ) D (p : A)

/-- raw包の源P代数構造は、基底射jと評価βの合成で与える。 -/
@[instance_reducible] def deltaPDivisionSourceRawAlgebra : Algebra P₀ B₀ := by
  exact deltaDivisionSourceRawAlgebra D (p : A) a₀

/-- raw包の源作用は、βで作用するAを経由する。 -/
theorem deltaPDivisionSourceRawTower :
    let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    let := deltaPDivisionSourceRawAlgebra (σ := σ) D y
    let : Module P₀ B₀ := Algebra.toModule
    @IsScalarTower P₀ A B₀
      (deltaDivisionSourceEvalAlgebra (σ := σ) D y).toSMul
      (inferInstance : Algebra A B₀).toSMul
      (deltaPDivisionSourceRawAlgebra (σ := σ) D y).toSMul := by
  exact deltaDivisionSourceRawTower D (p : A) a₀

/-- raw標準商射を源P上の代数射として表す。 -/
def deltaPDivisionSourceRawRight :
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := deltaPDivisionSourceRawAlgebra (σ := σ) D y
    letI : Module P₀ B₀ := Algebra.toModule
    P₀ →ₐ[P₀] B₀ := by
  exact deltaDivisionSourceRawRight D (p : A) a₀

/-- 通常テンソル積からraw包への実標準環射。 -/
def deltaPDivisionSourceTensorToRaw :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ →+* B₀ := by
  exact deltaDivisionSourceTensorToRaw D (p : A) a₀

/-- テンソルの純元の像は、既存基底射と既存商射の積。 -/
theorem deltaPDivisionSourceTensorToRaw_tmul (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    deltaPDivisionSourceTensorToRaw D y (a ⊗ₜ[P₀] b) = j₀ a * q₀ b := by
  exact deltaDivisionSourceTensorToRaw_tmul D (p : A) a₀ a b

/-- 通常テンソルの両因子の包含を保つ、raw包からの環射は一意に存在する。 -/
theorem existsUnique_deltaPDivisionRawTensorMap :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    ∃! k : B₀ →+* A ⊗[P₀] P₀,
      k.comp q₀ = Algebra.TensorProduct.includeRight.toRingHom ∧
      k.comp j₀ = Algebra.TensorProduct.includeLeftRingHom := by
  exact existsUnique_deltaDivisionRawTensorMap D (p : A) a₀

/-- raw包から通常テンソルへの実標準環射。 -/
def deltaPDivisionSourceRawToTensor :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    B₀ →+* A ⊗[P₀] P₀ := by
  exact deltaDivisionSourceRawToTensor D (p : A) a₀

/-- rawからテンソルへの射は、元の終域Lの標準像を右因子へ送る。 -/
theorem deltaPDivisionSourceRawToTensor_comp_quotient :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceRawToTensor D y).comp q₀ =
      Algebra.TensorProduct.includeRight.toRingHom := by
  exact deltaDivisionSourceRawToTensor_comp_quotient D (p : A) a₀

/-- rawからテンソルへの射は、元の基底Aの標準像を左因子へ送る。 -/
theorem deltaPDivisionSourceRawToTensor_comp_base :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceRawToTensor D y).comp j₀ = Algebra.TensorProduct.includeLeftRingHom := by
  exact deltaDivisionSourceRawToTensor_comp_base D (p : A) a₀

/-- 実通常テンソル積A⊗_P Lは、既存のraw δ除算包と標準的に環同型。 -/
def deltaPDivisionSourceTensorEquiv :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ ≃+* B₀ := by
  exact deltaDivisionSourceTensorEquiv D (p : A) a₀

/-- 通常テンソル比較同型の純元上の具体的な式。 -/
theorem deltaPDivisionSourceTensorEquiv_tmul (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    deltaPDivisionSourceTensorEquiv D y (a ⊗ₜ[P₀] b) = j₀ a * q₀ b := by
  exact deltaDivisionSourceTensorEquiv_tmul D (p : A) a₀ a b

/-- 通常テンソル比較同型の逆は、raw標準商元を右因子の標準像へ送る。 -/
theorem deltaPDivisionSourceTensorEquiv_symm_quotient (r : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceTensorEquiv D y).symm (q₀ r) = 1 ⊗ₜ[P₀] r := by
  exact deltaDivisionSourceTensorEquiv_symm_quotient D (p : A) a₀ r


end SerrePositivity.BhattScholze

end DeltaPDivisionSourceTensor

/-! ## 実自由δ射の通常テンソルと具体的分冪表示環

自由δ射の導来テンソルの離散性は主張しない。A上の導来完備化と実p還元は別に明示する。
-/

@[expose] public noncomputable section DeltaPDivisionSourcePrincipal

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "T₀" => TensorProduct P₀ A P₀
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "qraw₀" => Ideal.Quotient.mk
  (DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
    (deltaDivisionRelationIdeal (p : A) a₀))
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 指定した実自由δ射の通常テンソルと、分冪表示環との標準環同型。 -/
def deltaPDivisionSourcePrincipalEquiv
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    T₀ ≃+* PrincipalDPPresentation A y := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  exact (deltaPDivisionSourceTensorEquiv (σ := σ) D y).trans
    (deltaPDivisionRawPrincipalEquiv (σ := σ) hA hpA D y hg v hv hy)

/-- 全純テンソルの像は、左係数と右因子の実商像で計算できる。 -/
theorem deltaPDivisionSourcePrincipalEquiv_tmul
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    deltaPDivisionSourcePrincipalEquiv D y hA hpA hg v hv hy (a ⊗ₜ[P₀] b) =
      algebraMap A (PrincipalDPPresentation A y) a *
        deltaPDivisionRawPrincipalEquiv (σ := σ) hA hpA D y hg v hv hy (qraw₀ b) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  rw [deltaPDivisionSourcePrincipalEquiv, RingEquiv.trans_apply,
    deltaPDivisionSourceTensorEquiv_tmul, map_mul, deltaPDivisionRawPrincipalEquiv_coeff]

/-- 通常テンソル比較は、元の自然な左A係数作用を保つA代数同型。 -/
def deltaPDivisionSourcePrincipalAlgEquiv
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    T₀ ≃ₐ[A] PrincipalDPPresentation A y := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  refine { deltaPDivisionSourcePrincipalEquiv D y hA hpA hg v hv hy with commutes' := ?_ }
  intro a
  change deltaPDivisionSourcePrincipalEquiv D y hA hpA hg v hv hy (a ⊗ₜ[P₀] 1) = _
  rw [deltaPDivisionSourcePrincipalEquiv_tmul]
  simp only [map_one, mul_one]

/-- この通常テンソルを元のA→A/pで実導来還元した具体的比較。 -/
def deltaPDivisionSourcePrincipalDerivedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A T₀)) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  let e := (deltaPDivisionSourcePrincipalAlgEquiv D y hA hpA hg v hv hy).toLinearEquiv.toModuleIso
  exact (boundedAboveDerivedBaseChange q₀).mapIso (boundedAboveDerivedSingleFunctor.mapIso e) ≪≫
    principalDPRelativeDerivedModPIso y hA hpA hy

/-- 通常テンソルのA上の実導来完備化を実p還元した具体的比較。 -/
def deltaPDivisionSourcePrincipalCompletedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A T₀))) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  let e := (deltaPDivisionSourcePrincipalAlgEquiv D y hA hpA hg v hv hy).toLinearEquiv.toModuleIso
  exact (boundedAboveDerivedBaseChange q₀).mapIso
      ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).mapIso
        (boundedAboveDerivedSingleFunctor.mapIso e)) ≪≫
    principalDPRelativeCompletedDerivedModPIso y hA hpA hy

/-- 通常テンソルの実p比較も、元のA上の標準導来完備化単位と両立する。 -/
theorem deltaPDivisionSourcePrincipalCompletedModPIso_unit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).map
        ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A T₀))) ≫
      (deltaPDivisionSourcePrincipalCompletedModPIso D y hA hpA hg v hv hy).hom =
        (deltaPDivisionSourcePrincipalDerivedModPIso D y hA hpA hg v hv hy).hom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let e := boundedAboveDerivedSingleFunctor.mapIso
    (deltaPDivisionSourcePrincipalAlgEquiv D y hA hpA hg v hv hy).toLinearEquiv.toModuleIso
  let F := boundedAboveDerivedBaseChange q₀
  let C := DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
  let U := DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
  change F.map (U.app _) ≫
      (F.map (C.map e.hom) ≫ (principalDPRelativeCompletedDerivedModPIso y hA hpA hy).hom) =
    F.map e.hom ≫ (principalDPRelativeDerivedModPIso y hA hpA hy).hom
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ← U.naturality e.hom,
    CategoryTheory.Functor.map_comp, Category.assoc,
    principalDPRelativeCompletedDerivedModPIso_unit]
  rfl

end SerrePositivity.BhattScholze

end DeltaPDivisionSourcePrincipal

/-! ## G7交換入力を明示した実自由δ射の導来分冪比較

PreservesColimitの仮定自体はここでは証明しない。G7の解消や無条件のB4完成とは区別する。
-/

@[expose] public noncomputable section DeltaPDivisionSourceDerivedPrincipal

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D (p : A)
local notation "β₀" => deltaDivisionSourceEval D a₀
local notation "F₀" => deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 具体的なα:x↦pzとβ:x↦φ(y)の二つのTorを、既存の実導来対称性で比較する。 -/
def deltaPDivisionSourceTorSwapIso (n : ℕ) :
    (((Tor (ModuleCat.{u} P₀) n).obj Mβ).obj Mα) ≅
      (((Tor (ModuleCat.{u} P₀) n).obj Mα).obj Mβ) :=
  by
    let X : DerivedCategory.Minus (ModuleCat.{u} P₀) := boundedAboveDerivedSingleFunctor.obj Mβ
    let Y : DerivedCategory.Minus (ModuleCat.{u} P₀) := boundedAboveDerivedSingleFunctor.obj Mα
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) (-(n : ℤ))
    let es := boundedAboveDerivedTensorSymmetry (R := P₀) X Y
    let e₁ := ((boundedAboveDerivedTensorModuleTorNatIso (R := P₀) Mβ n).app Mα).symm
    let e₂ := H.mapIso (DerivedCategory.Minus.ι.mapIso es)
    let e₃ := (boundedAboveDerivedTensorModuleTorNatIso (R := P₀) Mα n).app Mβ
    exact e₁ ≪≫ e₂ ≪≫ e₃

/-- G7交換入力の下、実評価βに沿う終域Pの全高次Torは零。 -/
theorem deltaPDivisionSourceEval_torVanishing_of_preservesColimit
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    scalarExtensionTorVanishing β₀ Mα := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
      let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
      let : Subsingleton (((ModuleCat.extendScalars α₀).leftDerived (i + 1)).obj Mβ) :=
        deltaPDivisionSource_tor_subsingleton_of_preservesColimit D y hpA hg v hv hy i (hpres i)
      have hz : IsZero (((ModuleCat.extendScalars α₀).leftDerived (i + 1)).obj Mβ) :=
        ModuleCat.isZero_of_subsingleton _
      have hH := (derivedModuleBaseChangeHomologyIso α₀ (i + 1)).app Mβ
      have hzH := hH.isZero_iff.mpr hz
      have hzR := (ModuleCat.restrictScalars α₀).map_isZero hzH
      have hzT := ((derivedModuleBaseChangeTorIso α₀ (i + 1)).app Mβ).isZero_iff.mp hzR
      exact (deltaPDivisionSourceTorSwapIso D y (i + 1)).isZero_iff.mpr hzT

/-- 実評価βによる通常係数拡大は、指定した二つの作用による通常テンソルそのもの。 -/
def deltaPDivisionSourceEvalScalarEquiv :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    ((ModuleCat.extendScalars β₀).obj Mα) ≃ₗ[A] (A ⊗[P₀] P₀) := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  exact
    { toFun := fun z ↦ z
      invFun := fun z ↦ z
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- G7交換入力の下で、実自由δ射の導来拡大が具体的表示環の次数零対象となる。 -/
def deltaPDivisionSourceDerivedPrincipalIso_of_preservesColimit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    (boundedAboveDerivedBaseChange β₀).obj (boundedAboveDerivedSingleFunctor.obj Mα) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A (PrincipalDPPresentation A y)) := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  let e := (deltaPDivisionSourceEvalScalarEquiv (σ := σ) D y).trans
    (deltaPDivisionSourcePrincipalAlgEquiv D y hA hpA hg v hv hy).toLinearEquiv
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso β₀ Mα
      (deltaPDivisionSourceEval_torVanishing_of_preservesColimit D y hpA hg v hv hy hpres) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

/-- G7交換入力の下、実自由δ導来拡大をA→A/pで実導来還元する具体的比較。 -/
def deltaPDivisionSourceDerivedModPIso_of_preservesColimit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    (boundedAboveDerivedBaseChange q₀).obj
        ((boundedAboveDerivedBaseChange β₀).obj (boundedAboveDerivedSingleFunctor.obj Mα)) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) :=
  (boundedAboveDerivedBaseChange q₀).mapIso
      (deltaPDivisionSourceDerivedPrincipalIso_of_preservesColimit
        D y hA hpA hg v hv hy hpres) ≪≫
    principalDPRelativeDerivedModPIso y hA hpA hy

/-- 同じG7交換入力の下、実自由δ導来拡大のA上の実完備化のp還元を具体的表示環へ同定する。 -/
def deltaPDivisionSourceDerivedCompletedModPIso_of_preservesColimit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    (boundedAboveDerivedBaseChange q₀).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          ((boundedAboveDerivedBaseChange β₀).obj (boundedAboveDerivedSingleFunctor.obj Mα))) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) :=
  (boundedAboveDerivedBaseChange q₀).mapIso
      ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).mapIso
        (deltaPDivisionSourceDerivedPrincipalIso_of_preservesColimit
          D y hA hpA hg v hv hy hpres)) ≪≫
    principalDPRelativeCompletedDerivedModPIso y hA hpA hy

/-- G7交換入力付きの実自由δ導来比較は、標準A導来完備化単位と両立する。 -/
theorem deltaPDivisionSourceDerivedCompletedModPIso_unit_of_preservesColimit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    (boundedAboveDerivedBaseChange q₀).map
        ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          ((boundedAboveDerivedBaseChange β₀).obj (boundedAboveDerivedSingleFunctor.obj Mα))) ≫
      (deltaPDivisionSourceDerivedCompletedModPIso_of_preservesColimit
        D y hA hpA hg v hv hy hpres).hom =
        (deltaPDivisionSourceDerivedModPIso_of_preservesColimit
          D y hA hpA hg v hv hy hpres).hom := by
  let e := deltaPDivisionSourceDerivedPrincipalIso_of_preservesColimit
    D y hA hpA hg v hv hy hpres
  let F := boundedAboveDerivedBaseChange q₀
  let C := DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
  let U := DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
  change F.map (U.app _) ≫
      (F.map (C.map e.hom) ≫ (principalDPRelativeCompletedDerivedModPIso y hA hpA hy).hom) =
    F.map e.hom ≫ (principalDPRelativeDerivedModPIso y hA hpA hy).hom
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ← U.naturality e.hom,
    CategoryTheory.Functor.map_comp, Category.assoc,
    principalDPRelativeCompletedDerivedModPIso_unit]
  rfl

end SerrePositivity.BhattScholze

end DeltaPDivisionSourceDerivedPrincipal

/-! ## 実通常テンソルのp正則性と旧ねじれ商の標準比較

raw包の既存正則性と標準比較同型を利用する。G7やCFFを仮定した結論ではない。
-/

@[expose] public noncomputable section DeltaPDivisionSourceTensorRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "q₀" => Ideal.Quotient.mk
  (DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
    (deltaDivisionRelationIdeal (p : A) a₀))
include hpA hg hv hy

/-- 正則一元入力では、実自由δ射の通常テンソル積にpねじれがない。 -/
theorem deltaPDivisionSourceTensor_p_mul_injective :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    Function.Injective (fun x : A ⊗[P₀] P₀ => (p : A ⊗[P₀] P₀) * x) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let e := deltaPDivisionSourceTensorEquiv (σ := σ) D y
  have hp := deltaPDivisionRaw_p_mul_injective (σ := σ) D y hpA hg v hv hy
  intro x z hxz
  apply e.injective
  apply hp
  have h := congrArg e hxz
  simpa only [map_mul, map_natCast] using h

/-- 実通常テンソル積と、実導来完備化の既存入力となる旧ねじれ除去商との環同型。 -/
def deltaPDivisionSourceTensorTorsionEquiv :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ ≃+* DeltaDivisionTorsionQuotient D (p : A) a₀ := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  exact (deltaPDivisionSourceTensorEquiv D y).trans
    (deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy)

/-- 実通常テンソルと旧ねじれ商の同型は、両因子の標準像を保つ。 -/
theorem deltaPDivisionSourceTensorTorsionEquiv_tmul (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy (a ⊗ₜ[P₀] b) =
      deltaDivisionTorsionMap D (p : A) a₀ a * Ideal.Quotient.mk _ (q₀ b) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  rw [deltaPDivisionSourceTensorTorsionEquiv, RingEquiv.trans_apply,
    deltaPDivisionSourceTensorEquiv_tmul, map_mul,
    deltaPDivisionRawTorsionEquiv_apply, deltaPDivisionRawTorsionEquiv_apply]
  rfl

/-- 実通常テンソルから旧ねじれ商への比較は、元の基底Aの標準射を保つ。 -/
theorem deltaPDivisionSourceTensorTorsionEquiv_comp_base :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom.comp
      Algebra.TensorProduct.includeLeftRingHom = deltaDivisionTorsionMap D (p : A) a₀ := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  apply RingHom.ext
  intro a
  change deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy (a ⊗ₜ[P₀] 1) = _
  rw [deltaPDivisionSourceTensorTorsionEquiv_tmul, map_one, map_one, mul_one]

end SerrePositivity.BhattScholze

end DeltaPDivisionSourceTensorRegular

/-! ## 実通常テンソル入力と既存δ除算候補の実導来完備化H⁰比較

同型な通常入力環を、既存の環としての完備化普遍性で比較する。
G7・原典の導来δpushout比較・古典的完備化への置換は用いない。
-/

@[expose] public noncomputable section DeltaPDivisionSourceTensorCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "R₀" => TensorProduct P₀ A P₀
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "U₀" => DeltaDivisionTorsionQuotient D (p : A) a₀
local notation "d₀" => deltaDivisionTorsionMap D (p : A) a₀ (p : A)
local notation "C₀" => DerivedDeltaDivisionCompletion D (p : A) a₀
local notation "H₀" => PDCompletionH0 R₀ p (p : R₀)
include hpA hg hv hy

/-- 実通常テンソルの(p,p)導来完備化H⁰と既存候補は、標準単位を保つ環同型で一意に比較できる。 -/
theorem existsUnique_deltaPDivisionSourceTensorCompletionEquiv :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    ∃! e : H₀ ≃+* C₀,
      e.toRingHom.comp (pdCompletionUnit R₀ p (p : R₀)) =
        (pdCompletionUnit U₀ p d₀).comp
          (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  let E := deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy
  let jH := pdCompletionUnit R₀ p (p : R₀)
  let jC := pdCompletionUnit U₀ p d₀
  let f₀ := jC.comp E.toRingHom
  let g₀ := jH.comp E.symm.toRingHom
  have hpH := pdCompletionH0_self_complete_p R₀ p (p : R₀)
  have hdH := pdCompletionH0_self_complete_d R₀ p (p : R₀)
  have hpC := pdCompletionH0_self_complete_p U₀ p d₀
  have hdC := pdCompletionH0_self_complete_d U₀ p d₀
  have hfd : IsModuleComplete C₀ (f₀ (p : R₀)) (ModuleCat.of C₀ C₀) := by
    simpa only [map_natCast] using hpC
  have hdU : d₀ = (p : U₀) := map_natCast (deltaDivisionTorsionMap D (p : A) a₀) p
  have hgNat : g₀ d₀ = (p : H₀) := (congrArg g₀ hdU).trans (map_natCast g₀ p)
  have hgd : IsModuleComplete H₀ (g₀ d₀) (ModuleCat.of H₀ H₀) := by
    simpa only [hgNat] using hpH
  obtain ⟨f, hf, hfu⟩ := existsUnique_pdCompletionRingHom R₀ p (p : R₀) C₀ f₀ hpC hfd
  obtain ⟨g, hG, _⟩ := existsUnique_pdCompletionRingHom U₀ p d₀ H₀ g₀ hpH hgd
  have hfg : f.comp g = RingHom.id C₀ := by
    apply pdCompletionRingHom_ext U₀ p d₀ C₀ jC hpC hdC
    · rw [RingHom.comp_assoc, hG, ← RingHom.comp_assoc, hf]
      apply RingHom.ext
      intro r
      change jC (E (E.symm r)) = jC r
      rw [RingEquiv.apply_symm_apply]
    · exact RingHom.id_comp jC
  have hgf : g.comp f = RingHom.id H₀ := by
    apply pdCompletionRingHom_ext R₀ p (p : R₀) H₀ jH hpH hdH
    · rw [RingHom.comp_assoc, hf, ← RingHom.comp_assoc, hG]
      apply RingHom.ext
      intro r
      change jH (E.symm (E r)) = jH r
      rw [RingEquiv.symm_apply_apply]
    · exact RingHom.id_comp jH
  let e := RingEquiv.ofRingHom f g hfg hgf
  refine ⟨e, hf, ?_⟩
  intro e' he'
  apply RingEquiv.ext
  intro r
  exact RingHom.congr_fun (hfu e'.toRingHom he') r

/-- 標準単位で正規化した、実通常テンソルの実完備化H⁰と既存δ除算候補の環同型。 -/
def deltaPDivisionSourceTensorCompletionEquiv :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    H₀ ≃+* C₀ := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  letI := pdCompletionCommRing R₀ p (p : R₀)
  letI := derivedDeltaDivisionCommRing D (p : A) a₀
  exact Classical.choose (existsUnique_deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy)

/-- 実完備化比較は、元の通常入力環の標準単位を保つ。 -/
theorem deltaPDivisionSourceTensorCompletionEquiv_comp_unit :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).toRingHom.comp
      (pdCompletionUnit R₀ p (p : R₀)) =
        (pdCompletionUnit U₀ p d₀).comp
          (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  exact (Classical.choose_spec
    (existsUnique_deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy)).1

/-- 実完備化比較は、通常入力環の標準単位上で具体的な入力同型に一致する。 -/
theorem deltaPDivisionSourceTensorCompletionEquiv_unit :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    ∀ r : R₀,
      deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy
        (pdCompletionUnit R₀ p (p : R₀) r) =
      pdCompletionUnit U₀ p d₀ (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy r) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  intro r
  exact RingHom.congr_fun (deltaPDivisionSourceTensorCompletionEquiv_comp_unit D y hpA hg v hv hy) r

/-- 実完備化比較は、元のAから既存候補への標準射を保つ。 -/
theorem deltaPDivisionSourceTensorCompletionEquiv_comp_base :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).toRingHom.comp
      ((pdCompletionUnit R₀ p (p : R₀)).comp Algebra.TensorProduct.includeLeftRingHom) =
        derivedDeltaDivisionMap D (p : A) a₀ := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  rw [← RingHom.comp_assoc, deltaPDivisionSourceTensorCompletionEquiv_comp_unit,
    RingHom.comp_assoc, deltaPDivisionSourceTensorTorsionEquiv_comp_base]
  rfl

/-- 逆比較も、旧ねじれ商の実標準単位を実通常テンソル完備化の標準単位へ戻す。 -/
theorem deltaPDivisionSourceTensorCompletionEquiv_symm_unit (r : U₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).symm
      (pdCompletionUnit U₀ p d₀ r) =
        pdCompletionUnit R₀ p (p : R₀)
          ((deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).symm r) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  apply (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).injective
  rw [RingEquiv.apply_symm_apply, deltaPDivisionSourceTensorCompletionEquiv_unit,
    RingEquiv.apply_symm_apply]

end SerrePositivity.BhattScholze

end DeltaPDivisionSourceTensorCompletion

/-! ## 実通常テンソルのδ構造と両因子の標準包含

raw包のδ切断を標準比較同型とW₂写像で引き戻す。
-/

@[expose] public noncomputable section DeltaPDivisionSourceTensorDelta

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "R₀" => TensorProduct P₀ A P₀
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀

/-- 実通常テンソル上の、raw包の標準比較で引き戻した具体的δ構造。 -/
def deltaPDivisionSourceTensorDelta :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    DeltaStructure p R₀ := by
  exact deltaDivisionSourceTensorDelta D (p : A) a₀

/-- 実通常テンソルからraw包への標準環同型はδ構造を保存する。 -/
theorem deltaPDivisionSourceTensorEquiv_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceTensorDelta (σ := σ) D y).IsDeltaHom
      (deltaAdjoinDivisionStructure D (p : A) a₀)
      (deltaPDivisionSourceTensorEquiv D y).toRingHom := by
  exact deltaDivisionSourceTensorEquiv_isDeltaHom D (p : A) a₀

/-- raw包から実通常テンソルへの標準逆同型もδ構造を保存する。 -/
theorem deltaPDivisionSourceTensorEquiv_symm_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaAdjoinDivisionStructure D (p : A) a₀).IsDeltaHom
      (deltaPDivisionSourceTensorDelta (σ := σ) D y)
      (deltaPDivisionSourceTensorEquiv D y).symm.toRingHom := by
  exact deltaDivisionSourceTensorEquiv_symm_isDeltaHom D (p : A) a₀

/-- 通常テンソルの元の基底Aの標準包含はδ射。 -/
theorem deltaPDivisionSourceTensor_includeLeft_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    D.IsDeltaHom (deltaPDivisionSourceTensorDelta (σ := σ) D y)
      Algebra.TensorProduct.includeLeftRingHom := by
  exact deltaDivisionSourceTensor_includeLeft_isDeltaHom D (p : A) a₀

/-- 通常テンソルの終域自由δ環Lの標準包含もδ射。 -/
theorem deltaPDivisionSourceTensor_includeRight_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (relativeFreeDeltaStructure σ D).IsDeltaHom (deltaPDivisionSourceTensorDelta (σ := σ) D y)
      Algebra.TensorProduct.includeRight.toRingHom := by
  exact deltaDivisionSourceTensor_includeRight_isDeltaHom D (p : A) a₀

/-- 両因子の標準包含をδ射にするδ構造は、構成したものに一意に一致する。 -/
theorem deltaPDivisionSourceTensorDelta_unique :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    ∀ E : DeltaStructure p R₀,
      D.IsDeltaHom E Algebra.TensorProduct.includeLeftRingHom →
      (relativeFreeDeltaStructure σ D).IsDeltaHom E Algebra.TensorProduct.includeRight.toRingHom →
      E = deltaPDivisionSourceTensorDelta (σ := σ) D y := by
  exact deltaDivisionSourceTensorDelta_unique D (p : A) a₀


end SerrePositivity.BhattScholze

end DeltaPDivisionSourceTensorDelta

/-! ## 実通常テンソルの実導来完備化H⁰と標準比較のδ両立

実H⁰の既存δ延長と環射の普遍性を用いる。
原典の導来δpushout比較・分冪包比較・CFFはここでは結論しない。
-/

@[expose] public noncomputable section DeltaPDivisionSourceTensorCompletionDelta

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "R₀" => TensorProduct P₀ A P₀
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "U₀" => DeltaDivisionTorsionQuotient D (p : A) a₀
local notation "d₀" => deltaDivisionTorsionMap D (p : A) a₀ (p : A)
local notation "C₀" => DerivedDeltaDivisionCompletion D (p : A) a₀
local notation "H₀" => PDCompletionH0 R₀ p (p : R₀)

/-- 実通常テンソルの実(p,p)導来完備化H⁰上の、既存の標準δ延長。 -/
def deltaPDivisionSourceTensorCompletionDelta :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    DeltaStructure p H₀ := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  exact deltaPDCompletionStructure (deltaPDivisionSourceTensorDelta (σ := σ) D y) (p : R₀)

/-- 元の基底から通常テンソルの実導来完備化H⁰への標準射はδ射。 -/
theorem deltaPDivisionSourceTensorCompletion_base_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    D.IsDeltaHom (deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y)
      ((pdCompletionUnit R₀ p (p : R₀)).comp Algebra.TensorProduct.includeLeftRingHom) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  exact (pdCompletionUnit_isDeltaHom
    (deltaPDivisionSourceTensorDelta (σ := σ) D y) (p : R₀)).comp
      (deltaPDivisionSourceTensor_includeLeft_isDeltaHom (σ := σ) D y)

variable [Unique σ]
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
include hpA hg hv hy

/-- 正則一元入力の通常テンソルと旧ねじれ商の標準比較は両方向にδ射。 -/
theorem deltaPDivisionSourceTensorTorsionEquiv_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceTensorDelta (σ := σ) D y).IsDeltaHom
        (deltaDivisionTorsionStructure D (p : A) a₀)
        (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom ∧
      (deltaDivisionTorsionStructure D (p : A) a₀).IsDeltaHom
        (deltaPDivisionSourceTensorDelta (σ := σ) D y)
        (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).symm.toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  have h := deltaPDivisionRawTorsionEquiv_isDeltaHom (σ := σ) D y hpA hg v hv hy
  exact ⟨h.1.comp (deltaPDivisionSourceTensorEquiv_isDeltaHom (σ := σ) D y),
    (deltaPDivisionSourceTensorEquiv_symm_isDeltaHom (σ := σ) D y).comp h.2⟩

/-- 実導来完備化H⁰の標準比較同型は、両側の既存の標準δ延長と両立する。 -/
theorem deltaPDivisionSourceTensorCompletionEquiv_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    (deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y).IsDeltaHom
      (derivedDeltaDivisionStructure D (p : A) a₀)
      (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  let g := (pdCompletionUnit U₀ p d₀).comp
    (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom
  have hgδ := (pdCompletionUnit_isDeltaHom (deltaDivisionTorsionStructure D (p : A) a₀)
    d₀).comp (deltaPDivisionSourceTensorTorsionEquiv_isDeltaHom D y hpA hg v hv hy).1
  have hpC := pdCompletionH0_self_complete_p U₀ p d₀
  have hdC : IsModuleComplete C₀ (g (p : R₀)) (ModuleCat.of C₀ C₀) := by
    simpa only [map_natCast] using hpC
  exact pdCompletionRingHom_isDeltaHom (deltaPDivisionSourceTensorDelta (σ := σ) D y)
    (p : R₀) (derivedDeltaDivisionStructure D (p : A) a₀) g hgδ hpC hdC
      (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).toRingHom
      (deltaPDivisionSourceTensorCompletionEquiv_comp_unit D y hpA hg v hv hy)

/-- 実導来完備化H⁰の標準逆同型もδ射。 -/
theorem deltaPDivisionSourceTensorCompletionEquiv_symm_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    (derivedDeltaDivisionStructure D (p : A) a₀).IsDeltaHom
      (deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y)
      (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).symm.toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  let e := deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy
  intro r
  apply e.injective
  change e (e.symm ((derivedDeltaDivisionStructure D (p : A) a₀).delta r)) =
    e ((deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y).delta (e.symm r))
  rw [RingEquiv.apply_symm_apply]
  have h := deltaPDivisionSourceTensorCompletionEquiv_isDeltaHom D y hpA hg v hv hy (e.symm r)
  change e ((deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y).delta (e.symm r)) =
    (derivedDeltaDivisionStructure D (p : A) a₀).delta (e (e.symm r)) at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

end SerrePositivity.BhattScholze

end DeltaPDivisionSourceTensorCompletionDelta
