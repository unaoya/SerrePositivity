module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineAffineDivision
public import Mathlib.Algebra.MvPolynomial.Equiv
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineAffineDivision

/-!
# 結晶模型の未完備多項式座標

## 概要
未完備自由 δ 環の変数を、第 0 頂点の変数、頂点差、正の反復 δ 座標に分ける。

## 方針
通常の多項式環として、差を引く代入と足す代入が逆であることを示す。

## 規約
正の反復 δ 座標は δ^{a+1} の a で添字付ける。

## 使われ方
結晶側の p 除算環の分冪因子と通常の多項式因子の分離。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {k : Type u} [CommRing k] (r n : ℕ)

/-- 余分な反復 δ 座標の添字。 -/
abbrev CrystallineExtraIndex := (Fin r × ℕ) × Fin (n + 1)

private abbrev DifferenceIndex := ULift.{u} (Fin r × Fin n)

private abbrev ConstantIndex := Fin r ⊕ CrystallineExtraIndex r n

local notation "S" => AffineIndex r n × ℕ
local notation "T" => DifferenceIndex r n ⊕ ConstantIndex r n

private def toCoordVar (x : AffineIndex.{u} r n × ℕ) :
    MvPolynomial (DifferenceIndex.{u} r n ⊕ ConstantIndex r n) k :=
  let j := x.1.down.1
  let i := x.1.down.2
  match x.2 with
  | 0 => Fin.cases (MvPolynomial.X (.inr (.inl j)))
      (fun a => MvPolynomial.X (.inr (.inl j)) + MvPolynomial.X (.inl ⟨(j,a)⟩)) i
  | a + 1 => MvPolynomial.X (.inr (.inr ((j,a), i)))

private def fromCoordVar (x : DifferenceIndex.{u} r n ⊕ ConstantIndex r n) :
    MvPolynomial (AffineIndex.{u} r n × ℕ) k :=
  match x with
  | .inl d =>
      MvPolynomial.X (⟨(d.down.1, d.down.2.succ)⟩, 0) -
        MvPolynomial.X (⟨(d.down.1, 0)⟩, 0)
  | .inr (.inl j) => MvPolynomial.X (⟨(j, 0)⟩, 0)
  | .inr (.inr ((j,a),i)) => MvPolynomial.X (⟨(j, i)⟩, a + 1)

private def coordPolyEquiv : MvPolynomial (AffineIndex.{u} r n × ℕ) k ≃ₐ[k]
    MvPolynomial (DifferenceIndex.{u} r n ⊕ ConstantIndex r n) k :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval (toCoordVar r n))
    (MvPolynomial.aeval (fromCoordVar r n))
    (by
      apply MvPolynomial.algHom_ext
      intro x
      rcases x with d | (j | ⟨⟨j,a⟩,i⟩)
      · obtain ⟨⟨j,i⟩⟩ := d
        simp [fromCoordVar, toCoordVar]
      · simp [fromCoordVar, toCoordVar]
      · simp [fromCoordVar, toCoordVar])
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨⟨⟨j,i⟩⟩,a⟩
      cases a with
      | zero =>
          refine Fin.cases ?_ (fun d => ?_) i
          · simp [toCoordVar, fromCoordVar]
          · simp [toCoordVar, fromCoordVar]
      | succ a => simp [toCoordVar, fromCoordVar])

/-- 自由座標を、差の変数が外側にある二重多項式環へ移す。 -/
def crystallineRawCoordinateEquiv :
    MvPolynomial (AffineIndex.{u} r n × ℕ) k ≃+*
      MvPolynomial (ULift.{u} (Fin r × Fin n)) (MvPolynomial (Fin r ⊕ CrystallineExtraIndex r n) k) :=
  (coordPolyEquiv (k := k) r n).toRingEquiv.trans (MvPolynomial.sumRingEquiv k _ _)

/-- 第 0 頂点との差は、新しい多項式環の一つの変数になる。 -/
theorem crystallineRawCoordinateEquiv_diff (t : ULift.{u} (Fin r × Fin n)) :
    crystallineRawCoordinateEquiv (k := k) r n
      (MvPolynomial.X (⟨(t.down.1,t.down.2.succ)⟩,0) - MvPolynomial.X (⟨(t.down.1,0)⟩,0)) =
      MvPolynomial.X t := by
  obtain ⟨⟨j,i⟩⟩ := t
  let a : AffineIndex.{u} r n × ℕ := (⟨(j,i.succ)⟩, 0)
  let b : AffineIndex.{u} r n × ℕ := (⟨(j,0)⟩, 0)
  let c := MvPolynomial.sumRingEquiv k (DifferenceIndex.{u} r n) (ConstantIndex r n)
  have h : (MvPolynomial.aeval (R := k) (toCoordVar (k := k) r n))
      (MvPolynomial.X a - MvPolynomial.X b) =
      MvPolynomial.X (.inl ⟨(j,i)⟩) := by
    rw [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    simp [a, b, toCoordVar]
  exact (congrArg c h).trans (MvPolynomial.sumRingEquiv_X_inl k _ _ _)

theorem crystallineRawCoordinateEquiv_C (a : k) :
    crystallineRawCoordinateEquiv.{u} (k := k) r n (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  change MvPolynomial.sumRingEquiv k (DifferenceIndex.{u} r n) (ConstantIndex r n)
    ((coordPolyEquiv (k := k) r n) (MvPolynomial.C a)) = _
  rw [show coordPolyEquiv (k := k) r n (MvPolynomial.C a) = MvPolynomial.C a
    from (coordPolyEquiv (k := k) r n).commutes a]
  exact MvPolynomial.sumRingEquiv_C _ _ _ _

theorem crystallineRawCoordinateEquiv_base (j : Fin r) :
    crystallineRawCoordinateEquiv.{u} (k := k) r n (MvPolynomial.X (⟨(j,0)⟩,0)) =
      MvPolynomial.C (MvPolynomial.X (.inl j)) := by
  change MvPolynomial.sumRingEquiv k (DifferenceIndex.{u} r n) (ConstantIndex r n)
    ((MvPolynomial.aeval (R := k) (toCoordVar (k := k) r n)) (MvPolynomial.X (⟨(j,0)⟩,0))) = _
  rw [MvPolynomial.aeval_X]
  exact MvPolynomial.sumRingEquiv_X_inr _ _ _ _

theorem crystallineRawCoordinateEquiv_extra (j : Fin r) (i : Fin (n + 1)) (a : ℕ) :
    crystallineRawCoordinateEquiv.{u} (k := k) r n (MvPolynomial.X (⟨(j,i)⟩,a + 1)) =
      MvPolynomial.C (MvPolynomial.X (.inr ((j,a),i))) := by
  change MvPolynomial.sumRingEquiv k (DifferenceIndex.{u} r n) (ConstantIndex r n)
    ((MvPolynomial.aeval (R := k) (toCoordVar (k := k) r n))
      (MvPolynomial.X (⟨(j,i)⟩,a + 1))) = _
  rw [MvPolynomial.aeval_X]
  exact MvPolynomial.sumRingEquiv_X_inr _ _ _ _

end SerrePositivity.BhattScholze.Prismatic
