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
主定理には使われない。任意添字のモニック族の経路の部品のうち、BS 著者版 Corollary 2.39・BS 著者版 Corollary 2.44 の一般化に使える部分として残した（BS-W8）。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
BS の中には import 元がない（残した結果。`scripts/audit/bhatt_scholze.lean` が監査する）。
-/

universe u

/-! ## 余極限との比較の交換入力に相対的な全源評価環へのTor移送

標準MathlibのPreservesColimitを明示的に受け取る。
この入力自体を証明したり、余極限との比較を受領したりしたという主張ではない。
-/

@[expose] public noncomputable section DeltaPDivisionSourceColimitTor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D (p : A)
local notation "F₀" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y

/-- 余極限との比較の標準colimit交換入力があれば、全源評価環Aの正次数Torが零。
PreservesColimitの入力は未解消の共通基盤への要求として明示している。 -/
theorem Andre.deltaPDivisionSource_tor_subsingleton_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (i : ℕ)
    (hpres : PreservesColimit F₀ ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    Subsingleton (SerrePositivity.TorAlg α₀ (i + 1) A) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSource_tor_subsingleton_of_preservesColimit
    D (fun _ : σ => D.frobeniusLift y) α₀ i
    (fun N => _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceFinite_tor_subsingleton D y hpA hg v hv hy N i) hpres

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
open scoped _root_.TensorProduct
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
@[instance_reducible] def Andre.deltaPDivisionSourceTargetAlgebra : Algebra P₀ P₀ :=
  _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTargetAlgebra (σ := σ) D (p : A)

/-- raw包の源P代数構造は、基底射jと評価βの合成で与える。 -/
@[instance_reducible] def Andre.deltaPDivisionSourceRawAlgebra : Algebra P₀ B₀ := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceRawAlgebra D (p : A) a₀

/-- raw包の源作用は、βで作用するAを経由する。 -/
theorem Andre.deltaPDivisionSourceRawTower :
    let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceRawAlgebra (σ := σ) D y
    let : Module P₀ B₀ := Algebra.toModule
    @IsScalarTower P₀ A B₀
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y).toSMul
      (inferInstance : Algebra A B₀).toSMul
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceRawAlgebra (σ := σ) D y).toSMul := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceRawTower D (p : A) a₀

/-- raw標準商射を源P上の代数射として表す。 -/
def Andre.deltaPDivisionSourceRawRight :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceRawAlgebra (σ := σ) D y
    letI : Module P₀ B₀ := Algebra.toModule
    P₀ →ₐ[P₀] B₀ := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceRawRight D (p : A) a₀

/-- 通常テンソル積からraw包への実標準環射。 -/
def Andre.deltaPDivisionSourceTensorToRaw :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ →+* B₀ := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensorToRaw D (p : A) a₀

/-- テンソルの純元の像は、既存基底射と既存商射の積。 -/
theorem Andre.deltaPDivisionSourceTensorToRaw_tmul (a : A) (b : P₀) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorToRaw D y (a ⊗ₜ[P₀] b) = j₀ a * q₀ b := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensorToRaw_tmul D (p : A) a₀ a b

/-- 通常テンソルの両因子の包含を保つ、raw包からの環射は一意に存在する。 -/
theorem Andre.existsUnique_deltaPDivisionRawTensorMap :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    ∃! k : B₀ →+* A ⊗[P₀] P₀,
      k.comp q₀ = Algebra.TensorProduct.includeRight.toRingHom ∧
      k.comp j₀ = Algebra.TensorProduct.includeLeftRingHom := by
  exact _root_.SerrePositivity.BhattScholze.existsUnique_deltaDivisionRawTensorMap D (p : A) a₀

/-- raw包から通常テンソルへの実標準環射。 -/
def Andre.deltaPDivisionSourceRawToTensor :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    B₀ →+* A ⊗[P₀] P₀ := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceRawToTensor D (p : A) a₀

/-- rawからテンソルへの射は、元の終域Lの標準像を右因子へ送る。 -/
theorem Andre.deltaPDivisionSourceRawToTensor_comp_quotient :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceRawToTensor D y).comp q₀ =
      Algebra.TensorProduct.includeRight.toRingHom := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceRawToTensor_comp_quotient D (p : A) a₀

/-- rawからテンソルへの射は、元の基底Aの標準像を左因子へ送る。 -/
theorem Andre.deltaPDivisionSourceRawToTensor_comp_base :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceRawToTensor D y).comp j₀ = Algebra.TensorProduct.includeLeftRingHom := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceRawToTensor_comp_base D (p : A) a₀

/-- 実通常テンソル積A⊗_P Lは、既存のraw δ除算包と標準的に環同型。 -/
def Andre.deltaPDivisionSourceTensorEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ ≃+* B₀ := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensorEquiv D (p : A) a₀

/-- 通常テンソル比較同型の純元上の具体的な式。 -/
theorem Andre.deltaPDivisionSourceTensorEquiv_tmul (a : A) (b : P₀) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorEquiv D y (a ⊗ₜ[P₀] b) = j₀ a * q₀ b := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensorEquiv_tmul D (p : A) a₀ a b

/-- 通常テンソル比較同型の逆は、raw標準商元を右因子の標準像へ送る。 -/
theorem Andre.deltaPDivisionSourceTensorEquiv_symm_quotient (r : P₀) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorEquiv D y).symm (q₀ r) = 1 ⊗ₜ[P₀] r := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensorEquiv_symm_quotient D (p : A) a₀ r


end SerrePositivity.BhattScholze

end DeltaPDivisionSourceTensor

/-! ## 実自由δ射の通常テンソルと具体的分冪表示環

自由δ射の導来テンソルの離散性は主張しない。A上の導来完備化と実p還元は別に明示する。
-/

@[expose] public noncomputable section DeltaPDivisionSourcePrincipal

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
open scoped _root_.TensorProduct
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
def Andre.deltaPDivisionSourcePrincipalEquiv
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) → ℕ → _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    T₀ ≃+* _root_.SerrePositivity.BhattScholze.PrincipalDPPresentation A y := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorEquiv (σ := σ) D y).trans
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionRawPrincipalEquiv (σ := σ) hA hpA D y hg v hv hy)

/-- 全純テンソルの像は、左係数と右因子の実商像で計算できる。 -/
theorem Andre.deltaPDivisionSourcePrincipalEquiv_tmul
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) → ℕ → _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (a : A) (b : P₀) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourcePrincipalEquiv D y hA hpA hg v hv hy (a ⊗ₜ[P₀] b) =
      algebraMap A (_root_.SerrePositivity.BhattScholze.PrincipalDPPresentation A y) a *
        _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionRawPrincipalEquiv (σ := σ) hA hpA D y hg v hv hy (qraw₀ b) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourcePrincipalEquiv, RingEquiv.trans_apply,
    _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorEquiv_tmul, map_mul, _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionRawPrincipalEquiv_coeff]

/-- 通常テンソル比較は、元の自然な左A係数作用を保つA代数同型。 -/
def Andre.deltaPDivisionSourcePrincipalAlgEquiv
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) → ℕ → _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    T₀ ≃ₐ[A] _root_.SerrePositivity.BhattScholze.PrincipalDPPresentation A y := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  refine { _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourcePrincipalEquiv D y hA hpA hg v hv hy with commutes' := ?_ }
  intro a
  change _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourcePrincipalEquiv D y hA hpA hg v hv hy (a ⊗ₜ[P₀] 1) = _
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourcePrincipalEquiv_tmul]
  simp only [map_one, mul_one]

/-- この通常テンソルを元のA→A/pで実導来還元した具体的比較。 -/
def Andre.deltaPDivisionSourcePrincipalDerivedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) → ℕ → _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).obj
        (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A T₀)) ≅
      _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (_root_.SerrePositivity.BhattScholze.PrincipalDPPresentation Q₀ (q₀ y))) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  let e := (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourcePrincipalAlgEquiv D y hA hpA hg v hv hy).toLinearEquiv.toModuleIso
  exact (_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).mapIso (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.mapIso e) ≪≫
    _root_.SerrePositivity.BhattScholze.principalDPRelativeDerivedModPIso y hA hpA hy

/-- 通常テンソルのA上の実導来完備化を実p還元した具体的比較。 -/
def Andre.deltaPDivisionSourcePrincipalCompletedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) → ℕ → _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).obj
        ((_root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A T₀))) ≅
      _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (_root_.SerrePositivity.BhattScholze.PrincipalDPPresentation Q₀ (q₀ y))) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  let e := (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourcePrincipalAlgEquiv D y hA hpA hg v hv hy).toLinearEquiv.toModuleIso
  exact (_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).mapIso
      ((_root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).mapIso
        (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.mapIso e)) ≪≫
    _root_.SerrePositivity.BhattScholze.principalDPRelativeCompletedDerivedModPIso y hA hpA hy

/-- 通常テンソルの実p比較も、元のA上の標準導来完備化単位と両立する。 -/
theorem Andre.deltaPDivisionSourcePrincipalCompletedModPIso_unit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) → ℕ → _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).map
        ((_root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A T₀))) ≫
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourcePrincipalCompletedModPIso D y hA hpA hg v hv hy).hom =
        (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourcePrincipalDerivedModPIso D y hA hpA hg v hv hy).hom := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let e := _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.mapIso
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourcePrincipalAlgEquiv D y hA hpA hg v hv hy).toLinearEquiv.toModuleIso
  let F := _root_.SerrePositivity.boundedAboveDerivedBaseChange q₀
  let C := _root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
  let U := _root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
  change F.map (U.app _) ≫
      (F.map (C.map e.hom) ≫ (_root_.SerrePositivity.BhattScholze.principalDPRelativeCompletedDerivedModPIso y hA hpA hy).hom) =
    F.map e.hom ≫ (_root_.SerrePositivity.BhattScholze.principalDPRelativeDerivedModPIso y hA hpA hy).hom
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ← U.naturality e.hom,
    CategoryTheory.Functor.map_comp, Category.assoc,
    _root_.SerrePositivity.BhattScholze.principalDPRelativeCompletedDerivedModPIso_unit]
  rfl

end SerrePositivity.BhattScholze

end DeltaPDivisionSourcePrincipal

/-! ## 余極限との比較交換入力を明示した実自由δ射の導来分冪比較

PreservesColimitの仮定自体はここでは証明しない。余極限との比較の解消や無条件のB4完成とは区別する。
-/

@[expose] public noncomputable section DeltaPDivisionSourceDerivedPrincipal

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D (p : A)
local notation "β₀" => deltaDivisionSourceEval D a₀
local notation "F₀" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 具体的なα:x↦pzとβ:x↦φ(y)の二つのTorを、既存の実導来対称性で比較する。 -/
def Andre.deltaPDivisionSourceTorSwapIso (n : ℕ) :
    (((Tor (ModuleCat.{u} P₀) n).obj Mβ).obj Mα) ≅
      (((Tor (ModuleCat.{u} P₀) n).obj Mα).obj Mβ) :=
  by
    let X : DerivedCategory.Minus (ModuleCat.{u} P₀) := _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj Mβ
    let Y : DerivedCategory.Minus (ModuleCat.{u} P₀) := _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj Mα
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) (-(n : ℤ))
    let es := _root_.SerrePositivity.boundedAboveDerivedTensorSymmetry (R := P₀) X Y
    let e₁ := ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleTorNatIso (R := P₀) Mβ n).app Mα).symm
    let e₂ := H.mapIso (DerivedCategory.Minus.ι.mapIso es)
    let e₃ := (_root_.SerrePositivity.boundedAboveDerivedTensorModuleTorNatIso (R := P₀) Mα n).app Mβ
    exact e₁ ≪≫ e₂ ≪≫ e₃

/-- 余極限との比較交換入力の下、実評価βに沿う終域Pの全高次Torは零。 -/
theorem Andre.deltaPDivisionSourceEval_torVanishing_of_preservesColimit
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    _root_.SerrePositivity.scalarExtensionTorVanishing β₀ Mα := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
      let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
      let : Subsingleton (((ModuleCat.extendScalars α₀).leftDerived (i + 1)).obj Mβ) :=
        _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSource_tor_subsingleton_of_preservesColimit D y hpA hg v hv hy i (hpres i)
      have hz : IsZero (((ModuleCat.extendScalars α₀).leftDerived (i + 1)).obj Mβ) :=
        ModuleCat.isZero_of_subsingleton _
      have hH := (_root_.SerrePositivity.derivedModuleBaseChangeHomologyIso α₀ (i + 1)).app Mβ
      have hzH := hH.isZero_iff.mpr hz
      have hzR := (ModuleCat.restrictScalars α₀).map_isZero hzH
      have hzT := ((_root_.SerrePositivity.derivedModuleBaseChangeTorIso α₀ (i + 1)).app Mβ).isZero_iff.mp hzR
      exact (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTorSwapIso D y (i + 1)).isZero_iff.mpr hzT

/-- 実評価βによる通常係数拡大は、指定した二つの作用による通常テンソルそのもの。 -/
def Andre.deltaPDivisionSourceEvalScalarEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    ((ModuleCat.extendScalars β₀).obj Mα) ≃ₗ[A] (A ⊗[P₀] P₀) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  exact
    { toFun := fun z ↦ z
      invFun := fun z ↦ z
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- 余極限との比較交換入力の下で、実自由δ射の導来拡大が具体的表示環の次数零対象となる。 -/
def Andre.deltaPDivisionSourceDerivedPrincipalIso_of_preservesColimit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    (_root_.SerrePositivity.boundedAboveDerivedBaseChange β₀).obj (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj Mα) ≅
      _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A (_root_.SerrePositivity.BhattScholze.PrincipalDPPresentation A y)) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  let e := (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceEvalScalarEquiv (σ := σ) D y).trans
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourcePrincipalAlgEquiv D y hA hpA hg v hv hy).toLinearEquiv
  exact _root_.SerrePositivity.boundedAboveDerivedBaseChangeModuleAugmentationIso β₀ Mα
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceEval_torVanishing_of_preservesColimit D y hpA hg v hv hy hpres) ≪≫
    _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

/-- 余極限との比較交換入力の下、実自由δ導来拡大をA→A/pで実導来還元する具体的比較。 -/
def Andre.deltaPDivisionSourceDerivedModPIso_of_preservesColimit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    (_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).obj
        ((_root_.SerrePositivity.boundedAboveDerivedBaseChange β₀).obj (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj Mα)) ≅
      _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (_root_.SerrePositivity.BhattScholze.PrincipalDPPresentation Q₀ (q₀ y))) :=
  (_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).mapIso
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceDerivedPrincipalIso_of_preservesColimit
        D y hA hpA hg v hv hy hpres) ≪≫
    _root_.SerrePositivity.BhattScholze.principalDPRelativeDerivedModPIso y hA hpA hy

/-- 同じ余極限との比較交換入力の下、実自由δ導来拡大のA上の実完備化のp還元を具体的表示環へ同定する。 -/
def Andre.deltaPDivisionSourceDerivedCompletedModPIso_of_preservesColimit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    (_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).obj
        ((_root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          ((_root_.SerrePositivity.boundedAboveDerivedBaseChange β₀).obj (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj Mα))) ≅
      _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (_root_.SerrePositivity.BhattScholze.PrincipalDPPresentation Q₀ (q₀ y))) :=
  (_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).mapIso
      ((_root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).mapIso
        (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceDerivedPrincipalIso_of_preservesColimit
          D y hA hpA hg v hv hy hpres)) ≪≫
    _root_.SerrePositivity.BhattScholze.principalDPRelativeCompletedDerivedModPIso y hA hpA hy

/-- 余極限との比較交換入力付きの実自由δ導来比較は、標準A導来完備化単位と両立する。 -/
theorem Andre.deltaPDivisionSourceDerivedCompletedModPIso_unit_of_preservesColimit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    (_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).map
        ((_root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          ((_root_.SerrePositivity.boundedAboveDerivedBaseChange β₀).obj (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj Mα))) ≫
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceDerivedCompletedModPIso_of_preservesColimit
        D y hA hpA hg v hv hy hpres).hom =
        (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceDerivedModPIso_of_preservesColimit
          D y hA hpA hg v hv hy hpres).hom := by
  let e := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceDerivedPrincipalIso_of_preservesColimit
    D y hA hpA hg v hv hy hpres
  let F := _root_.SerrePositivity.boundedAboveDerivedBaseChange q₀
  let C := _root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
  let U := _root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
  change F.map (U.app _) ≫
      (F.map (C.map e.hom) ≫ (_root_.SerrePositivity.BhattScholze.principalDPRelativeCompletedDerivedModPIso y hA hpA hy).hom) =
    F.map e.hom ≫ (_root_.SerrePositivity.BhattScholze.principalDPRelativeDerivedModPIso y hA hpA hy).hom
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ← U.naturality e.hom,
    CategoryTheory.Functor.map_comp, Category.assoc,
    _root_.SerrePositivity.BhattScholze.principalDPRelativeCompletedDerivedModPIso_unit]
  rfl

end SerrePositivity.BhattScholze

end DeltaPDivisionSourceDerivedPrincipal

/-! ## 実通常テンソルのp正則性と旧ねじれ商の標準比較

raw包の既存正則性と標準比較同型を利用する。余極限との比較やCFFを仮定した結論ではない。
-/

@[expose] public noncomputable section DeltaPDivisionSourceTensorRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
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
theorem Andre.deltaPDivisionSourceTensor_p_mul_injective :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    Function.Injective (fun x : A ⊗[P₀] P₀ => (p : A ⊗[P₀] P₀) * x) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let e := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorEquiv (σ := σ) D y
  have hp := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionRaw_p_mul_injective (σ := σ) D y hpA hg v hv hy
  intro x z hxz
  apply e.injective
  apply hp
  have h := congrArg e hxz
  simpa only [map_mul, map_natCast] using h

/-- 実通常テンソル積と、実導来完備化の既存入力となる旧ねじれ除去商との環同型。 -/
def Andre.deltaPDivisionSourceTensorTorsionEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ ≃+* _root_.SerrePositivity.BhattScholze.DeltaDivisionTorsionQuotient D (p : A) a₀ := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorEquiv D y).trans
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy)

/-- 実通常テンソルと旧ねじれ商の同型は、両因子の標準像を保つ。 -/
theorem Andre.deltaPDivisionSourceTensorTorsionEquiv_tmul (a : A) (b : P₀) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy (a ⊗ₜ[P₀] b) =
      _root_.SerrePositivity.BhattScholze.deltaDivisionTorsionMap D (p : A) a₀ a * Ideal.Quotient.mk _ (q₀ b) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv, RingEquiv.trans_apply,
    _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorEquiv_tmul, map_mul,
    _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionRawTorsionEquiv_apply, _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionRawTorsionEquiv_apply]
  rfl

/-- 実通常テンソルから旧ねじれ商への比較は、元の基底Aの標準射を保つ。 -/
theorem Andre.deltaPDivisionSourceTensorTorsionEquiv_comp_base :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom.comp
      Algebra.TensorProduct.includeLeftRingHom = _root_.SerrePositivity.BhattScholze.deltaDivisionTorsionMap D (p : A) a₀ := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  apply RingHom.ext
  intro a
  change _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy (a ⊗ₜ[P₀] 1) = _
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv_tmul, map_one, map_one, mul_one]

end SerrePositivity.BhattScholze

end DeltaPDivisionSourceTensorRegular

/-! ## 実通常テンソル入力と既存δ除算候補の実導来完備化H⁰比較

同型な通常入力環を、既存の環としての完備化普遍性で比較する。
余極限との比較・原典の導来δpushout比較・古典的完備化への置換は用いない。
-/

@[expose] public noncomputable section DeltaPDivisionSourceTensorCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
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
theorem Andre.existsUnique_deltaPDivisionSourceTensorCompletionEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
    ∃! e : H₀ ≃+* C₀,
      e.toRingHom.comp (pdCompletionUnit R₀ p (p : R₀)) =
        (pdCompletionUnit U₀ p d₀).comp
          (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
  let E := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy
  let jH := pdCompletionUnit R₀ p (p : R₀)
  let jC := pdCompletionUnit U₀ p d₀
  let f₀ := jC.comp E.toRingHom
  let g₀ := jH.comp E.symm.toRingHom
  have hpH := _root_.SerrePositivity.BhattScholze.pdCompletionH0_self_complete_p R₀ p (p : R₀)
  have hdH := _root_.SerrePositivity.BhattScholze.pdCompletionH0_self_complete_d R₀ p (p : R₀)
  have hpC := _root_.SerrePositivity.BhattScholze.pdCompletionH0_self_complete_p U₀ p d₀
  have hdC := _root_.SerrePositivity.BhattScholze.pdCompletionH0_self_complete_d U₀ p d₀
  have hfd : IsModuleComplete C₀ (f₀ (p : R₀)) (ModuleCat.of C₀ C₀) := by
    simpa only [map_natCast] using hpC
  have hdU : d₀ = (p : U₀) := map_natCast (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionMap D (p : A) a₀) p
  have hgNat : g₀ d₀ = (p : H₀) := (congrArg g₀ hdU).trans (map_natCast g₀ p)
  have hgd : IsModuleComplete H₀ (g₀ d₀) (ModuleCat.of H₀ H₀) := by
    simpa only [hgNat] using hpH
  obtain ⟨f, hf, hfu⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_pdCompletionRingHom R₀ p (p : R₀) C₀ f₀ hpC hfd
  obtain ⟨g, hG, _⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_pdCompletionRingHom U₀ p d₀ H₀ g₀ hpH hgd
  have hfg : f.comp g = RingHom.id C₀ := by
    apply _root_.SerrePositivity.BhattScholze.pdCompletionRingHom_ext U₀ p d₀ C₀ jC hpC hdC
    · rw [RingHom.comp_assoc, hG, ← RingHom.comp_assoc, hf]
      apply RingHom.ext
      intro r
      change jC (E (E.symm r)) = jC r
      rw [RingEquiv.apply_symm_apply]
    · exact RingHom.id_comp jC
  have hgf : g.comp f = RingHom.id H₀ := by
    apply _root_.SerrePositivity.BhattScholze.pdCompletionRingHom_ext R₀ p (p : R₀) H₀ jH hpH hdH
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
def Andre.deltaPDivisionSourceTensorCompletionEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
    H₀ ≃+* C₀ := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  letI := pdCompletionCommRing R₀ p (p : R₀)
  letI := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
  exact Classical.choose (_root_.SerrePositivity.BhattScholze.Andre.existsUnique_deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy)

/-- 実完備化比較は、元の通常入力環の標準単位を保つ。 -/
theorem Andre.deltaPDivisionSourceTensorCompletionEquiv_comp_unit :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).toRingHom.comp
      (pdCompletionUnit R₀ p (p : R₀)) =
        (pdCompletionUnit U₀ p d₀).comp
          (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
  exact (Classical.choose_spec
    (_root_.SerrePositivity.BhattScholze.Andre.existsUnique_deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy)).1

/-- 実完備化比較は、通常入力環の標準単位上で具体的な入力同型に一致する。 -/
theorem Andre.deltaPDivisionSourceTensorCompletionEquiv_unit :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
    ∀ r : R₀,
      _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy
        (pdCompletionUnit R₀ p (p : R₀) r) =
      pdCompletionUnit U₀ p d₀ (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy r) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
  intro r
  exact RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv_comp_unit D y hpA hg v hv hy) r

/-- 実完備化比較は、元のAから既存候補への標準射を保つ。 -/
theorem Andre.deltaPDivisionSourceTensorCompletionEquiv_comp_base :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).toRingHom.comp
      ((pdCompletionUnit R₀ p (p : R₀)).comp Algebra.TensorProduct.includeLeftRingHom) =
        _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionMap D (p : A) a₀ := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
  rw [← RingHom.comp_assoc, _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv_comp_unit,
    RingHom.comp_assoc, _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv_comp_base]
  rfl

/-- 逆比較も、旧ねじれ商の実標準単位を実通常テンソル完備化の標準単位へ戻す。 -/
theorem Andre.deltaPDivisionSourceTensorCompletionEquiv_symm_unit (r : U₀) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).symm
      (pdCompletionUnit U₀ p d₀ r) =
        pdCompletionUnit R₀ p (p : R₀)
          ((_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).symm r) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
  apply (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).injective
  rw [RingEquiv.apply_symm_apply, _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv_unit,
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
def Andre.deltaPDivisionSourceTensorDelta :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    _root_.SerrePositivity.BhattScholze.DeltaStructure p R₀ := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensorDelta D (p : A) a₀

/-- 実通常テンソルからraw包への標準環同型はδ構造を保存する。 -/
theorem Andre.deltaPDivisionSourceTensorEquiv_isDeltaHom :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorDelta (σ := σ) D y).IsDeltaHom
      (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionStructure D (p : A) a₀)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorEquiv D y).toRingHom := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensorEquiv_isDeltaHom D (p : A) a₀

/-- raw包から実通常テンソルへの標準逆同型もδ構造を保存する。 -/
theorem Andre.deltaPDivisionSourceTensorEquiv_symm_isDeltaHom :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionStructure D (p : A) a₀).IsDeltaHom
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorDelta (σ := σ) D y)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorEquiv D y).symm.toRingHom := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensorEquiv_symm_isDeltaHom D (p : A) a₀

/-- 通常テンソルの元の基底Aの標準包含はδ射。 -/
theorem Andre.deltaPDivisionSourceTensor_includeLeft_isDeltaHom :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    D.IsDeltaHom (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorDelta (σ := σ) D y)
      Algebra.TensorProduct.includeLeftRingHom := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensor_includeLeft_isDeltaHom D (p : A) a₀

/-- 通常テンソルの終域自由δ環Lの標準包含もδ射。 -/
theorem Andre.deltaPDivisionSourceTensor_includeRight_isDeltaHom :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D).IsDeltaHom (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorDelta (σ := σ) D y)
      Algebra.TensorProduct.includeRight.toRingHom := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensor_includeRight_isDeltaHom D (p : A) a₀

/-- 両因子の標準包含をδ射にするδ構造は、構成したものに一意に一致する。 -/
theorem Andre.deltaPDivisionSourceTensorDelta_unique :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    ∀ E : _root_.SerrePositivity.BhattScholze.DeltaStructure p R₀,
      D.IsDeltaHom E Algebra.TensorProduct.includeLeftRingHom →
      (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D).IsDeltaHom E Algebra.TensorProduct.includeRight.toRingHom →
      E = _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorDelta (σ := σ) D y := by
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensorDelta_unique D (p : A) a₀


end SerrePositivity.BhattScholze

end DeltaPDivisionSourceTensorDelta

/-! ## 実通常テンソルの実導来完備化H⁰と標準比較のδ両立

実H⁰の既存δ延長と環射の普遍性を用いる。
原典の導来δpushout比較・分冪包比較・CFFはここでは結論しない。
-/

@[expose] public noncomputable section DeltaPDivisionSourceTensorCompletionDelta

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
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
def Andre.deltaPDivisionSourceTensorCompletionDelta :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    _root_.SerrePositivity.BhattScholze.DeltaStructure p H₀ := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  exact _root_.SerrePositivity.BhattScholze.deltaPDCompletionStructure (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorDelta (σ := σ) D y) (p : R₀)

/-- 元の基底から通常テンソルの実導来完備化H⁰への標準射はδ射。 -/
theorem Andre.deltaPDivisionSourceTensorCompletion_base_isDeltaHom :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    D.IsDeltaHom (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y)
      ((pdCompletionUnit R₀ p (p : R₀)).comp Algebra.TensorProduct.includeLeftRingHom) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  exact (_root_.SerrePositivity.BhattScholze.pdCompletionUnit_isDeltaHom
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorDelta (σ := σ) D y) (p : R₀)).comp
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensor_includeLeft_isDeltaHom (σ := σ) D y)

variable [Unique σ]
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
include hpA hg hv hy

/-- 正則一元入力の通常テンソルと旧ねじれ商の標準比較は両方向にδ射。 -/
theorem Andre.deltaPDivisionSourceTensorTorsionEquiv_isDeltaHom :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorDelta (σ := σ) D y).IsDeltaHom
        (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D (p : A) a₀)
        (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom ∧
      (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D (p : A) a₀).IsDeltaHom
        (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorDelta (σ := σ) D y)
        (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).symm.toRingHom := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  have h := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionRawTorsionEquiv_isDeltaHom (σ := σ) D y hpA hg v hv hy
  exact ⟨h.1.comp (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorEquiv_isDeltaHom (σ := σ) D y),
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorEquiv_symm_isDeltaHom (σ := σ) D y).comp h.2⟩

/-- 実導来完備化H⁰の標準比較同型は、両側の既存の標準δ延長と両立する。 -/
theorem Andre.deltaPDivisionSourceTensorCompletionEquiv_isDeltaHom :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y).IsDeltaHom
      (_root_.SerrePositivity.BhattScholze.derivedDeltaDivisionStructure D (p : A) a₀)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).toRingHom := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
  let g := (pdCompletionUnit U₀ p d₀).comp
    (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom
  have hgδ := (_root_.SerrePositivity.BhattScholze.pdCompletionUnit_isDeltaHom (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D (p : A) a₀)
    d₀).comp (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorTorsionEquiv_isDeltaHom D y hpA hg v hv hy).1
  have hpC := _root_.SerrePositivity.BhattScholze.pdCompletionH0_self_complete_p U₀ p d₀
  have hdC : IsModuleComplete C₀ (g (p : R₀)) (ModuleCat.of C₀ C₀) := by
    simpa only [map_natCast] using hpC
  exact _root_.SerrePositivity.BhattScholze.pdCompletionRingHom_isDeltaHom (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorDelta (σ := σ) D y)
    (p : R₀) (_root_.SerrePositivity.BhattScholze.derivedDeltaDivisionStructure D (p : A) a₀) g hgδ hpC hdC
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).toRingHom
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv_comp_unit D y hpA hg v hv hy)

/-- 実導来完備化H⁰の標準逆同型もδ射。 -/
theorem Andre.deltaPDivisionSourceTensorCompletionEquiv_symm_isDeltaHom :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
    (_root_.SerrePositivity.BhattScholze.derivedDeltaDivisionStructure D (p : A) a₀).IsDeltaHom
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).symm.toRingHom := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := _root_.SerrePositivity.BhattScholze.derivedDeltaDivisionCommRing D (p : A) a₀
  let e := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy
  intro r
  apply e.injective
  change e (e.symm ((_root_.SerrePositivity.BhattScholze.derivedDeltaDivisionStructure D (p : A) a₀).delta r)) =
    e ((_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y).delta (e.symm r))
  rw [RingEquiv.apply_symm_apply]
  have h := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionEquiv_isDeltaHom D y hpA hg v hv hy (e.symm r)
  change e ((_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y).delta (e.symm r)) =
    (_root_.SerrePositivity.BhattScholze.derivedDeltaDivisionStructure D (p : A) a₀).delta (e (e.symm r)) at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

end SerrePositivity.BhattScholze

end DeltaPDivisionSourceTensorCompletionDelta
