module

public import SerrePositivity.EInfinity.SimplexCuts.SignedNaturality
public import SerrePositivity.EInfinity.Surjection.Modules
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# 一般の切断和の自由加群への線形拡張

Berger–Fresse §2.2.6。正の arity の同じ基底語について全切断を足し、
係数と入力単体に関して双線形に延長する（5a-5a L06）。
正規化への降下や微分条件は、この自由加群上の定義とは別に証明する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 語長 (r+1)+d を、同じ切断区間数 r+d+1 として読む。 -/
def positiveWord {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) :
    Surjection.Word (r + 1) (r + d + 1) := by
  exact Eq.mp (congrArg (fun l => Surjection.Word (r + 1) l)
    (show (r + 1) + d = r + d + 1 by omega)) u

/-- 正の arity の BF 切断和。退化項は除外せず零として保持する。 -/
def cutSum (S : SSet.{0}) {r d q : ℕ} (u : Surjection.BasisWord (r + 1) d)
    (x : S _⦋q⦌) : (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ)) :=
  (eqToHom (congrArg (fun t : ℤ => (power (chains A S) (r + 1)).X t)
    (show -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) = -((d + q : ℕ) : ℤ) by
      congr 1; congr 1; omega))).hom
    (∑ s : Cut (r + d) q, cutTerm A S s (positiveWord u) x)

/-- L06 の双線形拡張。二つの自由加群の実生成元の値で定める。 -/
def rawComponent (S : SSet.{0}) (r d q : ℕ) :
    Surjection.degreeModule A (r + 1) d →ₗ[A]
      (((BarrattEccles.linearization A).obj S).obj (Opposite.op ⦋q⦌) →ₗ[A]
        (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ))) :=
  let V := (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ))
  let F := ((BarrattEccles.linearization A).obj S).obj (Opposite.op ⦋q⦌)
  (ModuleCat.freeDesc (M := ModuleCat.of A (F →ₗ[A] V))
    (↾fun u : ULift.{u} (Surjection.BasisWord (r + 1) d) =>
      (ModuleCat.freeDesc (M := V)
        (↾fun x : ULift.{u} (S _⦋q⦌) => cutSum A S u.down x.down)).hom)).hom

/-- 自由加群の実基底における値は、定義した同じ BF 切断和（BF §2.2.6）。 -/
lemma rawComponent_value (S : SSet.{0}) {r d q : ℕ}
    (u : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    rawComponent A S r d q (Surjection.basis A (r + 1) d (ULift.up u))
      (ModuleCat.freeMk (ULift.up x)) = cutSum A S u x := by
  change (ModuleCat.freeDesc (M := ModuleCat.of A
      ((((BarrattEccles.linearization A).obj S).obj (Opposite.op ⦋q⦌)) →ₗ[A]
        (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ))))
      (↾fun v : ULift.{u} (Surjection.BasisWord (r + 1) d) =>
        (ModuleCat.freeDesc (M := (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ)))
          (↾fun y : ULift.{u} (S _⦋q⦌) => cutSum A S v.down y.down)).hom))
      (ModuleCat.freeMk (ULift.up u)) (ModuleCat.freeMk (ULift.up x)) = _
  rw [ModuleCat.freeDesc_apply]
  exact ModuleCat.freeDesc_apply _ _


end SerrePositivity.EInfinity.SimplexCuts
