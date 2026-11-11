module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.LinearAlgebra.Span.Defs

/-!
概要：加群を一つの斉次元で局所化したときの次数成分を、通常の局所化内の部分加群で表す。
方針：各分母の冪で許される分子の像を取り、分母を一つ増やす写像でつなぐ。
規約：分母 fⁿ で許される分子の部分加群を V n として入力する。
使われ方：Proj の標準開の上で次数零局所化とその完全性を扱う。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- 局所化の分母としての f の冪。 -/
def projDenominator (f : S) (n : ℕ) : Submonoid.powers f :=
  ⟨f ^ n, ⟨n, rfl⟩⟩

private theorem projDenominator_succ (f : S) (n : ℕ) :
    projDenominator f (n + 1) = projDenominator f n * projDenominator f 1 := by
  apply Subtype.ext
  simp [projDenominator, pow_succ]

/-- 分子を V n に制限し、分母を fⁿ に固定した分数の線形写像。 -/
def projectiveGradedFraction (f : S) (V : ℕ → Submodule R M) (n : ℕ) :
    V n →ₗ[R] LocalizedModule (Submonoid.powers f) M :=
  (((LocalizedModule.divBy (projDenominator f n)).comp
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).restrictScalars R).comp
    (V n).subtype

/-- 分数写像は指定した分子と分母を持つ。 -/
theorem projectiveGradedFraction_apply (f : S) (V : ℕ → Submodule R M)
    (n : ℕ) (m : V n) :
    projectiveGradedFraction f V n m = LocalizedModule.mk m.val (projDenominator f n) := by
  simp [projectiveGradedFraction, LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk]

/-- 分母の指数すべてから、局所化の指定次数成分を作る。 -/
def projectiveGradedAway (f : S) (V : ℕ → Submodule R M) :
    Submodule R (LocalizedModule (Submonoid.powers f) M) :=
  ⨆ n, LinearMap.range (projectiveGradedFraction f V n)

/--
概要：分子の族が f の作用で次の部分へ移るなら、成分の元は一つの斉次分数で表される。
方針：分子と分母へ同時に f を掛けて像の列が増大することを示す。
規約：分母 f は非零因子とは仮定しない。
使われ方：次数零局所化の元を分子に戻して完全性を示す。
-/
theorem mem_projectiveGradedAway_iff (f : S) (V : ℕ → Submodule R M)
    (hstep : ∀ (n : ℕ) (m : V n), f • m.val ∈ V (n + 1))
    (z : LocalizedModule (Submonoid.powers f) M) :
    z ∈ projectiveGradedAway f V ↔ ∃ (n : ℕ) (m : V n), projectiveGradedFraction f V n m = z := by
  have hmono : Monotone (fun n ↦ LinearMap.range (projectiveGradedFraction f V n)) := by
    apply monotone_nat_of_le_succ
    intro n x hx
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hx
    refine LinearMap.mem_range.mpr ⟨⟨f • m.val, hstep n m⟩, ?_⟩
    rw [projectiveGradedFraction_apply, projectiveGradedFraction_apply, projDenominator_succ]
    simpa [projDenominator, Submonoid.smul_def] using
      (LocalizedModule.mk_cancel_common_right (projDenominator f n)
        (projDenominator f 1) m.val)
  rw [projectiveGradedAway, Submodule.mem_iSup_of_directed _ hmono.directed_le]
  simp only [LinearMap.mem_range]

section Map

variable {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- 分子の部分加群を保つ写像が、局所化の指定次数成分に誘導する写像。 -/
def projectiveGradedAwayMap (f : S) (V : ℕ → Submodule R M) (W : ℕ → Submodule R N)
    (g : M →ₗ[S] N) (hg : ∀ n, ∀ m ∈ V n, g m ∈ W n) :
    projectiveGradedAway f V →ₗ[R] projectiveGradedAway f W := by
  let U := Submonoid.powers f
  let G : LocalizedModule U M →ₗ[R] LocalizedModule U N :=
    (IsLocalizedModule.map U (LocalizedModule.mkLinearMap U M)
      (LocalizedModule.mkLinearMap U N) g).restrictScalars R
  have h : projectiveGradedAway f V ≤ (projectiveGradedAway f W).comap G := by
    apply iSup_le
    intro n y hy
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hy
    change G (projectiveGradedFraction f V n m) ∈ projectiveGradedAway f W
    apply (le_iSup (fun n ↦ LinearMap.range (projectiveGradedFraction f W n)) n)
    refine LinearMap.mem_range.mpr ⟨⟨g m.val, hg n m.val m.property⟩, ?_⟩
    simp only [projectiveGradedFraction_apply]
    exact (IsLocalizedModule.map_LocalizedModules U g m.val (projDenominator f n)).symm
  exact LinearMap.codRestrict _ (G.comp (projectiveGradedAway f V).subtype) (fun y ↦ h y.property)

/-- 指定次数の局所化写像は分子に元の写像を適用する。 -/
theorem projectiveGradedAwayMap_fraction (f : S) (V : ℕ → Submodule R M)
    (W : ℕ → Submodule R N) (g : M →ₗ[S] N) (hg : ∀ n, ∀ m ∈ V n, g m ∈ W n)
    (n : ℕ) (m : V n) (z : projectiveGradedAway f V)
    (hz : projectiveGradedFraction f V n m = z.val) :
    (projectiveGradedAwayMap f V W g hg z).val =
      projectiveGradedFraction f W n ⟨g m.val, hg n m.val m.property⟩ := by
  change IsLocalizedModule.map _ (LocalizedModule.mkLinearMap _ M)
    (LocalizedModule.mkLinearMap _ N) g z.val = _
  rw [← hz, projectiveGradedFraction_apply, projectiveGradedFraction_apply]
  exact IsLocalizedModule.map_LocalizedModules _ g m.val (projDenominator f n)

/-- 分子の各次数で全射なら、その局所化の指定次数成分でも全射になる。 -/
theorem projectiveGradedAwayMap_surjective (f : S) (V : ℕ → Submodule R M)
    (W : ℕ → Submodule R N) (g : M →ₗ[S] N) (hg : ∀ n, ∀ m ∈ V n, g m ∈ W n)
    (hstep : ∀ (n : ℕ) (m : W n), f • m.val ∈ W (n + 1))
    (hsurj : ∀ (n : ℕ) (w : W n), ∃ m : V n, g m.val = w.val) :
    Function.Surjective (projectiveGradedAwayMap f V W g hg) := by
  intro z
  obtain ⟨n, w, hw⟩ := (mem_projectiveGradedAway_iff f W hstep z.val).mp z.property
  obtain ⟨m, hm⟩ := hsurj n w
  let y : projectiveGradedAway f V :=
    ⟨projectiveGradedFraction f V n m,
      (le_iSup (fun n ↦ LinearMap.range (projectiveGradedFraction f V n)) n)
        (LinearMap.mem_range_self _ m)⟩
  refine ⟨y, Subtype.ext ?_⟩
  rw [projectiveGradedAwayMap_fraction f V W g hg n m y rfl, ← hw]
  congr 1
  exact Subtype.ext hm

variable {P : Type*} [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

/--
概要：分子の各次数で完全な二つの写像は、局所化の指定次数成分でも完全になる。
方針：局所化で零になる元の分子を f の冪で消し、分子の完全性で持ち上げる。
規約：同じ f の冪を分母にも掛けて次数を保つ。
使われ方：有限斉次自由表示を標準開 Čech の項ごとの完全列に移す。
-/
theorem projectiveGradedAwayMap_exact (f : S) (V : ℕ → Submodule R M)
    (W : ℕ → Submodule R N) (Z : ℕ → Submodule R P) (g : M →ₗ[S] N) (h : N →ₗ[S] P)
    (hg : ∀ n, ∀ m ∈ V n, g m ∈ W n) (hh : ∀ n, ∀ m ∈ W n, h m ∈ Z n)
    (hstepV : ∀ (n : ℕ) (m : V n), f • m.val ∈ V (n + 1))
    (hstepW : ∀ (n : ℕ) (m : W n), f • m.val ∈ W (n + 1))
    (hexact : ∀ (n : ℕ) (m : W n), h m.val = 0 ↔ ∃ v : V n, g v.val = m.val) :
    Function.Exact (projectiveGradedAwayMap f V W g hg) (projectiveGradedAwayMap f W Z h hh) := by
  intro y
  constructor
  · intro hy
    obtain ⟨n, m, hm⟩ := (mem_projectiveGradedAway_iff f W hstepW y.val).mp y.property
    have hzero : LocalizedModule.mk (h m.val) (projDenominator f n) = 0 := by
      have e := projectiveGradedAwayMap_fraction f W Z h hh n m y hm
      rw [hy, projectiveGradedFraction_apply] at e
      exact e.symm
    have hkill : ∃ a : Submonoid.powers f, a • h m.val = 0 := by
      rw [← LocalizedModule.zero_mk (1 : Submonoid.powers f), LocalizedModule.mk_eq] at hzero
      simpa using hzero
    obtain ⟨⟨_, d, rfl⟩, hd⟩ := hkill
    have hpow (j : ℕ) : f ^ j • m.val ∈ W (n + j) := by
      induction j with
      | zero => simp [m.property]
      | succ j ih =>
        simpa [pow_succ', mul_smul, Nat.add_assoc] using hstepW (n + j) ⟨_, ih⟩
    let m' : W (n + d) := ⟨f ^ d • m.val, hpow d⟩
    obtain ⟨v, hv⟩ := (hexact (n + d) m').mp (by
      change h (f ^ d • m.val) = 0
      rw [map_smul]
      exact hd)
    let x : projectiveGradedAway f V :=
      ⟨projectiveGradedFraction f V (n + d) v,
        (mem_projectiveGradedAway_iff f V hstepV _).mpr ⟨n + d, v, rfl⟩⟩
    refine ⟨x, Subtype.ext ?_⟩
    rw [projectiveGradedAwayMap_fraction f V W g hg (n + d) v x rfl, ← hm,
      projectiveGradedFraction_apply, projectiveGradedFraction_apply]
    change LocalizedModule.mk (g v.val) (projDenominator f (n + d)) =
      LocalizedModule.mk m.val (projDenominator f n)
    rw [hv, show projDenominator f (n + d) = projDenominator f n * projDenominator f d from
      Subtype.ext (pow_add f n d)]
    exact LocalizedModule.mk_cancel_common_right (projDenominator f n) (projDenominator f d) m.val
  · rintro ⟨x, rfl⟩
    obtain ⟨n, m, hm⟩ := (mem_projectiveGradedAway_iff f V hstepV x.val).mp x.property
    let m' : W n := ⟨g m.val, hg n m.val m.property⟩
    have hm' : projectiveGradedFraction f W n m' = (projectiveGradedAwayMap f V W g hg x).val :=
      (projectiveGradedAwayMap_fraction f V W g hg n m x hm).symm
    apply Subtype.ext
    rw [projectiveGradedAwayMap_fraction f W Z h hh n m' _ hm', projectiveGradedFraction_apply]
    change LocalizedModule.mk (h m'.val) (projDenominator f n) = 0
    rw [(hexact n m').mpr ⟨m, rfl⟩, LocalizedModule.zero_mk]

end Map

end SerrePositivity.AlgebraicGeometry
