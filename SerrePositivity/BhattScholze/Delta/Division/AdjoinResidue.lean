module
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaQuotient
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta

/-!
# δ 除算添加環の剰余とテンソル表示

概要：一般の構成とその比較をまとめる。
方針：元の型・本体・局所的な文脈を、機械的な名前の追従だけで保存する。
規約：特殊な包絡の存在や追加の仮定を導入しない。
使われ方：Bhatt–Scholze の包絡または perfectoid 化の比較。
-/

universe u v

/-! ## 既存δ除算添加環のraw (p,d)商の具体的表示 -/

@[expose] public noncomputable section DeltaAdjoinDivisionResiduePresentation

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)

/-- raw δ除算添加環における(p,基底dの像)の通常イデアル。 -/
def deltaAdjoinDivisionResidueIdeal : Ideal (DeltaAdjoinDivision D d a) :=
  Ideal.span {(p : DeltaAdjoinDivision D d a), deltaAdjoinDivisionMap D d a d}

/-- raw除算添加環の(p,d)商。ねじれ除去後のadic idealとは別の段階。 -/
abbrev DeltaAdjoinDivisionResidue :=
  DeltaAdjoinDivision D d a ⧸ deltaAdjoinDivisionResidueIdeal D d a

/-- raw環の残余イデアルは、無限自由環の(p,Cd)の標準商射による像。 -/
theorem deltaAdjoinDivisionResidueIdeal_eq_map :
    deltaAdjoinDivisionResidueIdeal D d a =
      Ideal.map (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal d a)))
        (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d}) := by
  rw [Ideal.map_span]
  simp only [Set.image_pair, map_natCast]
  rfl

/-- raw添加環の(p,d)商は、無限自由環で(p,Cd)とδ閉包を同時に課した商。 -/
def deltaAdjoinDivisionResidueSupEquiv :
    DeltaAdjoinDivisionResidue D d a ≃+*
      (RelativeFreeDeltaRing (R := A) σ ⧸
        (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
          (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))) :=
  (Ideal.quotEquivOfEq (deltaAdjoinDivisionResidueIdeal_eq_map D d a)).trans
    ((DoubleQuot.quotQuotEquivQuotSup
      ((relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d})).trans
      (Ideal.quotEquivOfEq (sup_comm _ _)))

/-- 二重商表示同型は元の無限自由環の標準像を同時商の標準像に送る。 -/
theorem deltaAdjoinDivisionResidueSupEquiv_mk (f : RelativeFreeDeltaRing (R := A) σ) :
    deltaAdjoinDivisionResidueSupEquiv D d a
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ f)) = Ideal.Quotient.mk _ f := by
  rw [deltaAdjoinDivisionResidueSupEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  change (Ideal.quotEquivOfEq (sup_comm _ _))
    (DoubleQuot.quotQuotEquivQuotSup
      ((relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d})
      (DoubleQuot.quotQuotMk
        ((relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))
        (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d}) f)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

/-- 基底係数上での二重商比較の標準写像図式。 -/
theorem deltaAdjoinDivisionResidueSupEquiv_coeff (b : A) :
    deltaAdjoinDivisionResidueSupEquiv D d a
      (Ideal.Quotient.mk _ (deltaAdjoinDivisionMap D d a b)) =
      Ideal.Quotient.mk _ (MvPolynomial.C b) :=
  deltaAdjoinDivisionResidueSupEquiv_mk D d a (MvPolynomial.C b)

end SerrePositivity.BhattScholze

end DeltaAdjoinDivisionResiduePresentation

/-! ## 実残余自由δ射の通常テンソルとraw(p,d)商

既存の通常pushout比較と標準テンソル商比較を合成する。
完備化・Tor消滅・対象残余商のδ構造は要求しない。
-/

@[expose] public noncomputable section DeltaDivisionSourceResidueTensor

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (c : σ → A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : P₀), MvPolynomial.C d}
local notation "Q₀" => P₀ ⧸ I₀
local notation "B₀" => DeltaAdjoinDivision D d c
local notation "R₀" => DeltaAdjoinDivisionResidue D d c
local notation "j₀" => deltaAdjoinDivisionMap D d c
local notation "q₀" => Ideal.Quotient.mk
  (DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D) (deltaDivisionRelationIdeal d c))

/-- 実残余自由δ射による源作用。標準商代数構造を既存のα作用から誘導する。 -/
@[instance_reducible] def deltaDivisionSourceResidueTargetAlgebra : Algebra P₀ Q₀ := by
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  infer_instance

/-- 実残余源作用の係数射は、標準商射と自由δ射αの合成そのもの。 -/
theorem deltaDivisionSourceResidueTargetAlgebra_algebraMap :
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
    letI : Module P₀ Q₀ := Algebra.toModule
    algebraMap P₀ Q₀ = (Ideal.Quotient.mk I₀).comp
      (deltaDivisionSourceMap (σ := σ) D d) := rfl

/-- 通常pushout比較の下で、右因子の(p,Cd)イデアルはraw包の実(p,d)イデアルとなる。 -/
theorem deltaDivisionSourceTensor_residueIdeal_map :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    ((I₀).map (Algebra.TensorProduct.includeRight (R := P₀) (A := A) (B := P₀)).toRingHom).map
      (deltaDivisionSourceTensorEquiv D d c).toRingHom = deltaAdjoinDivisionResidueIdeal D d c := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  rw [Ideal.map_map]
  have he : (deltaDivisionSourceTensorEquiv D d c).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := P₀) (A := A) (B := P₀)).toRingHom = q₀ := by
    apply RingHom.ext
    intro r
    change deltaDivisionSourceTensorEquiv D d c (1 ⊗ₜ[P₀] r) = q₀ r
    rw [deltaDivisionSourceTensorEquiv_tmul, map_one, one_mul]
  rw [he]
  exact (deltaAdjoinDivisionResidueIdeal_eq_map D d c).symm

/-- 実残余通常テンソルは、既存rawδ包の実(p,d)商と標準的に環同型。 -/
def deltaDivisionSourceResidueTensorEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
    letI : Module P₀ Q₀ := Algebra.toModule
    A ⊗[P₀] Q₀ ≃+* R₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
  letI : Module P₀ Q₀ := Algebra.toModule
  exact (Algebra.TensorProduct.tensorQuotientEquiv (R := P₀) A P₀ A I₀).toRingEquiv.trans
    (Ideal.quotientEquiv _ _ (deltaDivisionSourceTensorEquiv D d c)
      (deltaDivisionSourceTensor_residueIdeal_map D d c).symm)

/-- 残余テンソル比較は、各純テンソルを標準基底像と標準商像の積へ送る。 -/
theorem deltaDivisionSourceResidueTensorEquiv_tmul (a : A) (r : P₀) :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
    letI : Module P₀ Q₀ := Algebra.toModule
    deltaDivisionSourceResidueTensorEquiv D d c (a ⊗ₜ[P₀] Ideal.Quotient.mk I₀ r) =
      Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal D d c) (j₀ a * q₀ r) := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  let := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
  let : Module P₀ Q₀ := Algebra.toModule
  change Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal D d c)
    (deltaDivisionSourceTensorEquiv D d c (a ⊗ₜ[P₀] r)) = _
  rw [deltaDivisionSourceTensorEquiv_tmul]

/-- 実残余テンソル比較は元の係数A作用を保つ。 -/
def deltaDivisionSourceResidueTensorAlgEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
    letI : Module P₀ Q₀ := Algebra.toModule
    A ⊗[P₀] Q₀ ≃ₐ[A] R₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
  letI : Module P₀ Q₀ := Algebra.toModule
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionSourceResidueTensorEquiv D d c)
  intro a
  change deltaDivisionSourceResidueTensorEquiv D d c (a ⊗ₜ[P₀] 1) =
    Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal D d c) (j₀ a)
  have h := deltaDivisionSourceResidueTensorEquiv_tmul D d c a 1
  simpa only [map_one, mul_one] using h

end SerrePositivity.BhattScholze

end DeltaDivisionSourceResidueTensor
