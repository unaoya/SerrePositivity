module

public import SerrePositivity.BhattScholze.Prismatic.Envelopes.VariableEnvelopeBaseChange
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittCrystallinePrism
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittCrystallinePrism

/-!
# Witt 係数への有限 affine 枠の底変換

## 概要
標準の有限 affine 項を ψ に沿って完備底変換した環は、Witt 側の自由 δ 環で表される。

## 方針
有限 affine 包の台と基底射を自由 δ 環の標準基底射と照合する。
⑤c の完備自由 δ 環の底変換を適用し、標準の底変換脚上で式を残す。

## 規約
ここで扱うのは項ごとの完備テンソル積。余単体の底変換には構造射との照合を別に使う。

## 使われ方
BS 著者版 Theorem 6.4 の結晶の橋を Witt 上の模型に移す。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)]
variable (hP : IsBoundedPrism P) (r n : ℕ) (κ : Cardinal.{u})
variable (hκ : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ)

local notation "W" => WittVector p (A ⧸ P.ideal)
local notation "P'" => wittCrystallinePrism hpC
local notation "X" => affineEnvelopeTerm P hP r n κ hκ
local notation "S" => AffineIndex r n

omit [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)] in
private theorem standard_affine_base :
    (X).X.toHom.toRingHom = completedFreeDeltaBase P S :=
  affineEnvelopeUnit_base P r n

/-- 標準の有限包の台を自由 δ 環として読んだ変数。 -/
def affineFreeVariable (s : AffineIndex.{u} r n) : (X).X.B :=
  completedFreeDeltaVariable P S s

/-- ψ に沿う有限 affine 項の完備テンソル積を Witt 係数の自由 δ 環で表す。 -/
theorem exists_wittAffineBaseChange_equiv :
    letI := (psiRing P hpA).toAlgebra
    letI := (X).X.toHom.toRingHom.toAlgebra
    ∃ e : PrismCompletedTensor (A := A) (C := (X).X.B) P' ≃+* completedFreeDelta P' S,
      e.toRingHom.comp (prismCompletedTensorLeft P') = completedFreeDeltaBase P' S ∧
      ∀ s : S, e (prismCompletedTensorRight P' (affineFreeVariable P hP r n κ hκ s)) =
        completedFreeDeltaVariable P' S s := by
  rw [standard_affine_base P hP r n κ hκ]
  obtain ⟨e, _, hl, hx⟩ := exists_completedFreeDelta_baseChange_equiv
    P P' (psiPrism P hpA hpC) S
  refine ⟨?_, ?_, ?_⟩
  · simpa only [psiPrism, affineEnvelopeTerm, affineEnvelopeTermAux] using e
  · simpa only [psiPrism, affineEnvelopeTerm, affineEnvelopeTermAux, id_eq] using hl
  · intro s
    simpa only [psiPrism, affineEnvelopeTerm, affineEnvelopeTermAux, affineFreeVariable, id_eq] using hx s

end SerrePositivity.BhattScholze.Prismatic
