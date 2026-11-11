module

public import SerrePositivity.AlgebraicGeometry.AdicProjectionFactor
public import SerrePositivity.AlgebraicGeometry.LinearRangeDescent

/-!
概要：核の一様評価を使い、射影先の互換族を I 進剰余類へ戻す。
方針：十分先の射影の像を、元の加群の Iⁿ による商へ降ろす。
規約：像の安定化は、各互換族の成分が射影の像に入るという形で使う。
使われ方：Čech 形式関数の完備化比較の逆写像の成分。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R H : Type*} [CommRing R] [AddCommGroup H] [Module R H]
variable (I : Ideal R) {Q : ℕ → Type*}
variable [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)]
variable (π : ∀ n, H →ₗ[R] Q n)
variable (c : ℕ) (hker : ∀ n, LinearMap.ker (π (n + c)) ≤ I ^ n • (⊤ : Submodule R H))

/-- 十分先の射影の像から、元の加群の Iⁿ による商への線形写像。 -/
def adicProjectionImageToQuotient (n : ℕ) :
    LinearMap.range (π (n + c)) →ₗ[R] H ⧸ (I ^ n • (⊤ : Submodule R H)) :=
  linearRangeDescent (π (n + c)) (I ^ n • (⊤ : Submodule R H)).mkQ
    (by simpa only [Submodule.ker_mkQ] using hker n)

/-- 像から I 進剰余類への写像は、元の代表をそのまま剰余類に送る。 -/
@[simp] theorem adicProjectionImageToQuotient_rangeRestrict (n : ℕ) (m : H) :
    adicProjectionImageToQuotient I π c hker n ((π (n + c)).rangeRestrict m) =
      (I ^ n • (⊤ : Submodule R H)).mkQ m :=
  linearRangeDescent_rangeRestrict _ _ _ m

variable (t : ∀ i j : ℕ, j ≤ i → Q i →ₗ[R] Q j)
variable (himage : ∀ x : compatibleLinearFamilies t, ∀ n, x.val n ∈ LinearMap.range (π n))

/-- 互換族を、その成分が属する射影の像へ評価する線形写像。 -/
def compatibleLinearFamiliesEvalToRange (n : ℕ) :
    compatibleLinearFamilies t →ₗ[R] LinearMap.range (π n) :=
  (compatibleLinearFamiliesEval t n).codRestrict (LinearMap.range (π n)) (fun x ↦ himage x n)

/-- 射影先の互換族を、第 n 番目の I 進剰余類へ戻す線形写像。 -/
def adicProjectionCompatibleComponent (n : ℕ) :
    compatibleLinearFamilies t →ₗ[R] H ⧸ (I ^ n • (⊤ : Submodule R H)) :=
  (adicProjectionImageToQuotient I π c hker n).comp
    (compatibleLinearFamiliesEvalToRange π t himage (n + c))

/-- 互換族の十分先の成分を代表で書けば、戻した成分は同じ代表の剰余類。 -/
theorem adicProjectionCompatibleComponent_eq_mk (n : ℕ)
    (x : compatibleLinearFamilies t) (m : H) (hm : π (n + c) m = x.val (n + c)) :
    adicProjectionCompatibleComponent I π c hker t himage n x =
      (I ^ n • (⊤ : Submodule R H)).mkQ m := by
  have he : (⟨x.val (n + c), himage x (n + c)⟩ : LinearMap.range (π (n + c))) =
      (π (n + c)).rangeRestrict m := Subtype.ext hm.symm
  change adicProjectionImageToQuotient I π c hker n
    ⟨x.val (n + c), himage x (n + c)⟩ = _
  rw [he, adicProjectionImageToQuotient_rangeRestrict]

variable (hπ : ∀ i j (h : j ≤ i), (t i j h).comp (π i) = π j)
include hπ

/-- 戻した各 I 進剰余類は、通常の I 進遷移について互換。 -/
theorem adicProjectionCompatibleComponent_transition (i j : ℕ) (h : j ≤ i)
    (x : compatibleLinearFamilies t) :
    AdicCompletion.transitionMap I H h (adicProjectionCompatibleComponent I π c hker t himage i x) =
      adicProjectionCompatibleComponent I π c hker t himage j x := by
  obtain ⟨m, hm⟩ := himage x (i + c)
  have hmj : π (j + c) m = x.val (j + c) := by
    calc
      π (j + c) m = t (i + c) (j + c) (Nat.add_le_add_right h c) (π (i + c) m) :=
        (DFunLike.congr_fun (hπ (i + c) (j + c) (Nat.add_le_add_right h c)) m).symm
      _ = t (i + c) (j + c) (Nat.add_le_add_right h c) (x.val (i + c)) :=
        congrArg (t (i + c) (j + c) (Nat.add_le_add_right h c)) hm
      _ = x.val (j + c) := x.property _ _ _
  rw [adicProjectionCompatibleComponent_eq_mk I π c hker t himage i x m hm,
    adicProjectionCompatibleComponent_eq_mk I π c hker t himage j x m hmj]
  rfl

omit c hker hπ himage in
/-- 遷移の像が十分先で射影の像に入れば、互換族の各成分も射影の像に入る。 -/
theorem compatibleLinearFamilies_mem_range_of_stable
    (hstable : ∀ n, ∃ i, ∃ h : n ≤ i, LinearMap.range (t i n h) ≤ LinearMap.range (π n))
    (x : compatibleLinearFamilies t) (n : ℕ) : x.val n ∈ LinearMap.range (π n) := by
  obtain ⟨i, h, hi⟩ := hstable n
  exact hi ⟨x.val i, x.property i n h⟩

end SerrePositivity.AlgebraicGeometry
