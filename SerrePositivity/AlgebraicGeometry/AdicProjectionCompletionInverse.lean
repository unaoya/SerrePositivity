module

public import SerrePositivity.AlgebraicGeometry.AdicProjectionInverseComponents

/-!
概要：核の一様評価と像への所属から、互換族と I 進完備化の線形同型を得る。
方針：逆写像の成分の互換性を使い、両方の合成を代表上で計算する。
規約：完備化は Mathlib の AdicCompletion をそのまま使う。
使われ方：射影 Čech 版の形式関数に、実際の核・像の評価を代入する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R H : Type*} [CommRing R] [AddCommGroup H] [Module R H]
variable (I : Ideal R) {Q : ℕ → Type*}
variable [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)]
variable (π : ∀ n, H →ₗ[R] Q n)
variable (c : ℕ) (hker : ∀ n, LinearMap.ker (π (n + c)) ≤ I ^ n • (⊤ : Submodule R H))
variable (t : ∀ i j : ℕ, j ≤ i → Q i →ₗ[R] Q j)
variable (himage : ∀ x : compatibleLinearFamilies t, ∀ n, x.val n ∈ LinearMap.range (π n))
variable (hπ : ∀ i j (h : j ≤ i), (t i j h).comp (π i) = π j)

/-- 射影先の互換族から、元の加群の I 進完備化への線形写像。 -/
def adicProjectionCompletionInverse : compatibleLinearFamilies t →ₗ[R] AdicCompletion I H where
  toFun x := ⟨fun n ↦ adicProjectionCompatibleComponent I π c hker t himage n x, by
    intro m n h
    exact adicProjectionCompatibleComponent_transition I π c hker t himage hπ n m h x⟩
  map_add' x y := Subtype.ext (funext fun n ↦
    (adicProjectionCompatibleComponent I π c hker t himage n).map_add x y)
  map_smul' r x := Subtype.ext (funext fun n ↦
    (adicProjectionCompatibleComponent I π c hker t himage n).map_smul r x)

variable (hpow : ∀ n, I ^ n • (⊤ : Submodule R H) ≤ LinearMap.ker (π n))

/-- 互換族から戻す写像は、完備化からの標準写像の左逆。 -/
theorem adicProjectionCompletionInverse_left_inverse :
    Function.LeftInverse (adicProjectionCompletionInverse I π c hker t himage hπ)
      (adicProjectionCompletionMap I π hpow t hπ) := by
  intro a
  apply Subtype.ext
  funext n
  obtain ⟨m, hm⟩ := (I ^ (n + c) • (⊤ : Submodule R H)).mkQ_surjective (a.val (n + c))
  have hrep : π (n + c) m =
      (adicProjectionCompletionMap I π hpow t hπ a).val (n + c) := by
    change π (n + c) m = adicProjectionQuotientMap I π hpow (n + c) (a.val (n + c))
    rw [← hm]
    rfl
  change adicProjectionCompatibleComponent I π c hker t himage n
    (adicProjectionCompletionMap I π hpow t hπ a) = a.val n
  rw [adicProjectionCompatibleComponent_eq_mk I π c hker t himage n _ m hrep]
  change AdicCompletion.transitionMap I H (Nat.le_add_right n c)
    ((I ^ (n + c) • (⊤ : Submodule R H)).mkQ m) = a.val n
  exact (congrArg (AdicCompletion.transitionMap I H (Nat.le_add_right n c)) hm).trans
    (a.property (Nat.le_add_right n c))

/-- 互換族から戻す写像は、完備化からの標準写像の右逆。 -/
theorem adicProjectionCompletionInverse_right_inverse :
    Function.RightInverse (adicProjectionCompletionInverse I π c hker t himage hπ)
      (adicProjectionCompletionMap I π hpow t hπ) := by
  intro x
  apply Subtype.ext
  funext n
  obtain ⟨m, hm⟩ := himage x (n + c)
  change adicProjectionQuotientMap I π hpow n
    (adicProjectionCompatibleComponent I π c hker t himage n x) = x.val n
  rw [adicProjectionCompatibleComponent_eq_mk I π c hker t himage n x m hm]
  change π n m = x.val n
  calc
    π n m = t (n + c) n (Nat.le_add_right n c) (π (n + c) m) :=
      (DFunLike.congr_fun (hπ (n + c) n (Nat.le_add_right n c)) m).symm
    _ = t (n + c) n (Nat.le_add_right n c) (x.val (n + c)) :=
      congrArg (t (n + c) n (Nat.le_add_right n c)) hm
    _ = x.val n := x.property _ _ _

/-- 核の一様評価と像への所属から得られる、I 進完備化と互換族の線形同型。 -/
def adicProjectionCompletionLinearEquiv :
    AdicCompletion I H ≃ₗ[R] compatibleLinearFamilies t where
  toLinearMap := adicProjectionCompletionMap I π hpow t hπ
  invFun := adicProjectionCompletionInverse I π c hker t himage hπ
  left_inv := adicProjectionCompletionInverse_left_inverse I π c hker t himage hπ hpow
  right_inv := adicProjectionCompletionInverse_right_inverse I π c hker t himage hπ hpow

/-- 完備化同型の順写像は、標準写像そのもの。 -/
@[simp] theorem adicProjectionCompletionLinearEquiv_apply (a : AdicCompletion I H) :
    adicProjectionCompletionLinearEquiv I π c hker t himage hπ hpow a =
      adicProjectionCompletionMap I π hpow t hπ a := rfl

end SerrePositivity.AlgebraicGeometry
