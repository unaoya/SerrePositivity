module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.CartierCompletedForms
public import SerrePositivity.CommutativeAlgebra.DeRham.CartierFiniteGenerators
public import SerrePositivity.CommutativeAlgebra.DeRham.CartierFiniteProduct
public import Mathlib.Algebra.Field.IsField

/-!
# 結晶基底上の有限多項式 Cartier 同型

## 概要
結晶基底の剰余体上で有限 Cartier の加法同型と、その積・生成元の公式をまとめる。

## 方針
剰余体を素数体と同一視して係数の Frobenius を消す。

## 規約
零次の係数は `formsZeroEquiv` で形式へ移す。

## 使われ方
多項式 Hodge–Tate 比較。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.DeRham

variable (p : ℕ) [Fact p.Prime]

/-- 有限多項式の inverse Cartier と、外積・生成元での値。 -/
structure PolynomialCartier (n : ℕ) where
  app (i : ℕ) : forms (cartierBase.{u} p) (formVars.{u} n) i ≃+
    (deRhamComplex (cartierBase.{u} p) (formVars.{u} n)).homology i
  on_zero (f : Poly (cartierBase.{u} p) (formVars.{u} n)) :
    app 0 (formsZeroEquiv _ _ f) = cartierZeroClass _ _ p (cartierBase_natCast p) f
  on_one (t : formVars.{u} n) : app 1 (dX (cartierBase.{u} p) _ t) = cartierOneClass _ _ p t
  mul {i j : ℕ} (ω : forms (cartierBase.{u} p) (formVars.{u} n) i)
      (η : forms (cartierBase.{u} p) (formVars.{u} n) j) :
    app (i+j) (wedge _ _ ω η) = deRhamCohomologyWedge _ _ (app i ω) (app j η)

/-- 結晶基底の剰余体上の有限多項式の inverse Cartier 同型。 -/
def finitePolynomialCartier (n : ℕ) : PolynomialCartier.{u} p n := by
  let e := cartierBaseEquiv.{u} p
  letI : Field (cartierBase.{u} p) := (e.toMulEquiv.isField (Field.toIsField (ZMod p))).toField
  letI : CharP (cartierBase.{u} p) p := charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  letI : LinearOrder (formVars.{u} n) := LinearOrder.lift' ULift.down ULift.down_injective
  let F := finiteCartierLinearEquiv (cartierBase.{u} p) (formVars.{u} n) p (Fact.out : p.Prime).pos
  refine ⟨fun i => (F i).toAddEquiv, ?_, ?_, ?_⟩
  · intro f
    apply finiteCartierLinearEquiv_zero
    intro c
    apply e.injective
    rw [map_pow, ZMod.pow_card]
  · exact finiteCartierLinearEquiv_dX _ _ p (Fact.out : p.Prime).pos
  · exact finiteCartierLinearEquiv_wedge _ _ p (Fact.out : p.Prime).pos

end SerrePositivity.BhattScholze.Prismatic
