module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
概要：異なる係数環・イデアルの I 進完備化の間に、半線形写像を作る。
方針：各イデアル冪の作用を保つ写像を、各剰余類へ降ろす。
規約：flat 性を仮定せず、イデアルの像の包含から連続性を得る。
使われ方：底変換・閉厚化・Frobenius に対する形式関数の自然性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R S H K : Type*} [CommRing R] [CommRing S]
variable [AddCommGroup H] [Module R H] [AddCommGroup K] [Module S K]
variable (I : Ideal R) (J : Ideal S) {σ : R →+* S} (f : H →ₛₗ[σ] K)

/-- イデアルの像の包含から、半線形写像は各イデアル冪の作用を保つ。 -/
theorem adicSemilinear_smul_top_le_comap (hIJ : I.map σ ≤ J) (n : ℕ) :
    I ^ n • (⊤ : Submodule R H) ≤ (J ^ n • (⊤ : Submodule S K)).comap f := by
  have hI : I ≤ J.comap σ := Ideal.map_le_iff_le_comap.mp hIJ
  have hn : I ^ n ≤ (J ^ n).comap σ :=
    (pow_le_pow_left' hI n).trans (Ideal.le_comap_pow (f := σ) (K := J) n)
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m _hm
    change f (r • m) ∈ J ^ n • (⊤ : Submodule S K)
    rw [map_smulₛₗ]
    exact Submodule.smul_mem_smul (hn hr) Submodule.mem_top
  · intro x y hx hy
    change f (x + y) ∈ J ^ n • (⊤ : Submodule S K)
    rw [map_add]
    exact Submodule.add_mem (J ^ n • (⊤ : Submodule S K)) hx hy

variable (hmem : ∀ n, I ^ n • (⊤ : Submodule R H) ≤
  (J ^ n • (⊤ : Submodule S K)).comap f)

/-- 各イデアル冪による剰余類の間の半線形写像。 -/
def adicSemilinearQuotientMap (n : ℕ) :
    H ⧸ (I ^ n • (⊤ : Submodule R H)) →ₛₗ[σ] K ⧸ (J ^ n • (⊤ : Submodule S K)) :=
  (I ^ n • (⊤ : Submodule R H)).mapQ (J ^ n • (⊤ : Submodule S K)) f (hmem n)

/-- 剰余類の半線形写像は、元の代表をそのまま送る。 -/
@[simp] theorem adicSemilinearQuotientMap_mk (n : ℕ) (x : H) :
    adicSemilinearQuotientMap I J f hmem n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) := rfl

/-- 剰余類の半線形写像は、通常の I 進・J 進遷移と可換。 -/
theorem adicSemilinearQuotientMap_transition (i j : ℕ) (h : j ≤ i) :
    (AdicCompletion.transitionMap J K h).comp (adicSemilinearQuotientMap I J f hmem i) =
      (adicSemilinearQuotientMap I J f hmem j).comp (AdicCompletion.transitionMap I H h) := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (I ^ i • (⊤ : Submodule R H)) x (fun m ↦ ?_)
  rfl

/-- イデアル冪を保つ半線形写像が誘導する、Mathlib の完備化の間の半線形写像。 -/
def adicSemilinearCompletionMap : AdicCompletion I H →ₛₗ[σ] AdicCompletion J K where
  toFun a := ⟨fun n ↦ adicSemilinearQuotientMap I J f hmem n (a.val n), by
    intro j i h
    have hc := DFunLike.congr_fun (adicSemilinearQuotientMap_transition I J f hmem i j h)
      (a.val i)
    change AdicCompletion.transitionMap J K h (adicSemilinearQuotientMap I J f hmem i (a.val i)) =
      adicSemilinearQuotientMap I J f hmem j (AdicCompletion.transitionMap I H h (a.val i)) at hc
    exact hc.trans (congrArg (adicSemilinearQuotientMap I J f hmem j) (a.property h))⟩
  map_add' a b := Subtype.ext (funext fun n ↦
    (adicSemilinearQuotientMap I J f hmem n).map_add (a.val n) (b.val n))
  map_smul' r a := Subtype.ext (funext fun n ↦
    map_smulₛₗ (adicSemilinearQuotientMap I J f hmem n) r (a.val n))

/-- 半線形な完備化写像の成分は、剰余類の半線形写像で計算できる。 -/
@[simp] theorem adicSemilinearCompletionMap_apply (a : AdicCompletion I H) (n : ℕ) :
    (adicSemilinearCompletionMap I J f hmem a).val n =
      adicSemilinearQuotientMap I J f hmem n (a.val n) := rfl

/-- 半線形な完備化写像は、元の加群の写像と両立する。 -/
@[simp] theorem adicSemilinearCompletionMap_of_apply (x : H) (n : ℕ) :
    (adicSemilinearCompletionMap I J f hmem (AdicCompletion.of I H x)).val n =
      (AdicCompletion.of J K (f x)).val n := rfl

end SerrePositivity.AlgebraicGeometry
