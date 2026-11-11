module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.RepresentationComplex
public import SerrePositivity.EInfinity.BarrattEccles.Theory.ArityFreeRepresentation
public import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Arity の表現の圏の鎖複体

## 概要
HA 3.2.4.7 の二色比較の係数として、実際の Barratt–Eccles 複体を表現の圏で読む。

## 方針
右作用を逆元で左作用へ変え、次数 q をコチェイン次数 −q から制限する。

## 規約
正則表現の既存の同型を使い、標数や群の位数の可逆性は仮定しない。

## 使われ方
二色部分群へ制限する前の arity の射影解像度の台。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 実際の arity の複体の、逆元を使った左群作用。 -/
def arityComplexAction (n : ℕ) : ULift.{u} (Equiv.Perm (Fin n)) →* End (complex A n) where
  toFun σ := .of (complexRightAction A n σ.down⁻¹)
  map_one' := by
    apply End.ext
    change complexRightAction A n (1 : Equiv.Perm (Fin n))⁻¹ = 𝟙 _
    rw [inv_one, complexRightAction_one]
  map_mul' σ τ := by
    apply End.ext
    change complexRightAction A n (σ.down * τ.down)⁻¹ =
      complexRightAction A n τ.down⁻¹ ≫ complexRightAction A n σ.down⁻¹
    rw [mul_inv_rev, complexRightAction_mul]

/-- 複体の作用の各次数は、既存の正則 arity 表現と同じ。 -/
lemma arityComplexAction_degree (n q : ℕ) :
    complexDegreeRepresentation (arityComplexAction A n) (-(q : ℤ)) =
      arityDegreeRepresentation A n q := by
  ext σ x
  rfl

/-- 正規化鎖と同じ次数を持つ、表現の圏の arity 鎖複体。 -/
def arityRepresentationChain (n : ℕ) :
    ChainComplex (Rep.{u} A (ULift.{u} (Equiv.Perm (Fin n)))) ℕ :=
  (representationCochainComplex (arityComplexAction A n)).restriction ComplexShape.embeddingDownNat

/-- Arity の鎖複体は次数ごとに射影的である。 -/
lemma arityRepresentationChain_projective (n q : ℕ) :
    Projective ((arityRepresentationChain A n).X q) := by
  change Projective (Rep.of (complexDegreeRepresentation (arityComplexAction A n) (-(q : ℤ))))
  rw [arityComplexAction_degree]
  exact Projective.of_iso (arityDegreeFreeIso A n q) inferInstance

end SerrePositivity.EInfinity.BarrattEccles
