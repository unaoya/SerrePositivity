module

public import SerrePositivity.AlgebraicGeometry.LinearCompatibleFamilies
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
概要：Iⁿ を殺す互換な射影から、I 進完備化上の線形写像を作る。
方針：各射影を Iⁿ による商へ降ろし、Mathlib の完備化を成分ごとに評価する。
規約：ここでは Noether 性や有限生成性は仮定しない。
使われ方：Čech 形式関数の、完備化から閉厚化の互換族への標準写像。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R H : Type*} [CommRing R] [AddCommGroup H] [Module R H]
variable (I : Ideal R) {Q : ℕ → Type*}
variable [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)]
variable (π : ∀ n, H →ₗ[R] Q n)
variable (hpow : ∀ n, I ^ n • (⊤ : Submodule R H) ≤ LinearMap.ker (π n))

/-- IⁿH を殺す射影を、通常の I 進剰余類上へ降ろす。 -/
def adicProjectionQuotientMap (n : ℕ) :
    H ⧸ (I ^ n • (⊤ : Submodule R H)) →ₗ[R] Q n :=
  (I ^ n • (⊤ : Submodule R H)).liftQ (π n) (hpow n)

/-- I 進剰余類上の射影は、代表上で元の射影と一致。 -/
@[simp] theorem adicProjectionQuotientMap_mk (n : ℕ) (x : H) :
    adicProjectionQuotientMap I π hpow n (Submodule.Quotient.mk x) = π n x := rfl

variable (t : ∀ i j : ℕ, j ≤ i → Q i →ₗ[R] Q j)
variable (hπ : ∀ i j (h : j ≤ i), (t i j h).comp (π i) = π j)

include hπ

/-- 射影の互換性は、I 進剰余類からの写像にも降りる。 -/
theorem adicProjectionQuotientMap_transition (i j : ℕ) (h : j ≤ i) :
    (t i j h).comp (adicProjectionQuotientMap I π hpow i) =
      (adicProjectionQuotientMap I π hpow j).comp (AdicCompletion.transitionMap I H h) := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (I ^ i • (⊤ : Submodule R H)) x (fun m ↦ ?_)
  exact DFunLike.congr_fun (hπ i j h) m

/-- I 進完備化から、射影先の互換族への標準線形写像。 -/
def adicProjectionCompletionMap : AdicCompletion I H →ₗ[R] compatibleLinearFamilies t where
  toFun a := ⟨fun n ↦ adicProjectionQuotientMap I π hpow n (a.val n), by
    intro i j h
    have hc := DFunLike.congr_fun (adicProjectionQuotientMap_transition I π hpow t hπ i j h)
      (a.val i)
    change t i j h (adicProjectionQuotientMap I π hpow i (a.val i)) =
      adicProjectionQuotientMap I π hpow j (AdicCompletion.transitionMap I H h (a.val i)) at hc
    exact hc.trans (congrArg (adicProjectionQuotientMap I π hpow j) (a.property h))⟩
  map_add' a b := Subtype.ext (funext fun n ↦
    (adicProjectionQuotientMap I π hpow n).map_add (a.val n) (b.val n))
  map_smul' r a := Subtype.ext (funext fun n ↦
    (adicProjectionQuotientMap I π hpow n).map_smul r (a.val n))

/-- 標準写像を加群の元に評価すると、元の射影の族になる。 -/
@[simp] theorem adicProjectionCompletionMap_of_apply (x : H) (n : ℕ) :
    (adicProjectionCompletionMap I π hpow t hπ (AdicCompletion.of I H x)).val n = π n x := rfl

end SerrePositivity.AlgebraicGeometry
