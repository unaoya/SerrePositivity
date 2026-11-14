module


public meta import SerrePositivity.Util.Citation
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# 中心局所化の台判定

## 概要
自己準同型加群の局所化の比較から、対象の局所化での消滅と恒等射の中心冪ねじれを同定する。

## 方針
IsLocalizedModule の零元の検出を恒等射へ適用し、対象の消滅を恒等射の零性で判定する。

## 規約
自己準同型の比較自体は compact 性・T2 から供給する入力として明示する。
TT 局所化や (3.6) 全体の証明と数えない。係数代数の可換性は要求しない。

## 使われ方
論文 (3.6) 直後の中心局所化の台判定、TT Propositions 5.2.2–5.2.4・Theorem 7.4 への接続。
-/

@[expose] public section

universe u v w t r

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {R : Type r} [CommRing R]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type w} [Category.{t} D] [Preadditive D] [Linear R D]
  (F : C ⥤ D) [F.Additive] [F.Linear R] (s : R) (P : C)

/-- 概要：中心元での局所化後の消滅は恒等射の冪ねじれと同値（論文 (3.6)）。
方針：局所化の零元検出と IsZero の恒等射判定を合成する。
規約：自己準同型の局所化比較を明示的に仮定し、その compact 性による実現は T2 に委ねる。
使われ方：非可換係数を許す perfect 対象の中心台の判定。 -/
theorem centralLocalization_isZero_iff
    [IsLocalizedModule (Submonoid.powers s) (F.mapLinearMap R : (P ⟶ P) →ₗ[R] _)] :
    IsZero (F.obj P) ↔ ∃ n : ℕ, s ^ n • (𝟙 P) = 0 := by
  rw [IsZero.iff_id_eq_zero, ← F.map_id P]
  change (F.mapLinearMap R) (𝟙 P) = 0 ↔ _
  rw [IsLocalizedModule.eq_zero_iff (Submonoid.powers s) (F.mapLinearMap R)]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨n, hn⟩ := a.property
    refine ⟨n, ?_⟩
    change a.val • (𝟙 P) = 0 at ha
    exact (congrArg (fun r : R ↦ r • (𝟙 P)) hn).trans ha
  · rintro ⟨n, hn⟩
    exact ⟨⟨s ^ n, ⟨n, rfl⟩⟩, hn⟩

/-- 概要：恒等射を殺す中心冪は指数を増やしても恒等射を殺す（論文 (3.6)）。
方針：冪の積と加群作用の結合則を使う。
規約：対象の可換な自己準同型環は不要。使われ方：有限生成イデアルの共通指数。 -/
theorem central_power_kills_id_mono {m n : ℕ} (hmn : m ≤ n)
    (hm : s ^ m • (𝟙 P) = 0) : s ^ n • (𝟙 P) = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn
  rw [hk, Nat.add_comm m k, pow_add, mul_smul, hm, smul_zero]

omit F in
/-- 概要：有限個の中心元の冪で恒等射を殺す条件は共通指数を持つ（論文 (3.6)）。
方針：各指数の有限最大値を取り、冪ねじれの単調性を使う。
規約：空の生成系も含む。使われ方：有限生成中心イデアルの台条件。 -/
theorem central_finite_power_annihilation {ι : Type*} [Finite ι] (z : ι → R) :
    (∀ i, ∃ n : ℕ, z i ^ n • (𝟙 P) = 0) ↔
      ∃ n : ℕ, ∀ i, z i ^ n • (𝟙 P) = 0 := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · intro h
    choose e he using h
    refine ⟨Finset.univ.sup e, fun i ↦ ?_⟩
    exact central_power_kills_id_mono (z i) P (Finset.le_sup (Finset.mem_univ i)) (he i)
  · rintro ⟨n, hn⟩ i
    exact ⟨n, hn i⟩

omit F in
/-- 概要：有限個の中心局所化での消滅は共通中心冪による恒等射の消滅と同値（論文 (3.6)）。
方針：各自己準同型の局所化比較を恒等射へ適用し、有限最大値で指数を統一する。
規約：局所化先の圏は生成元ごとに異なってよい。比較は compact 性から供給すべき入力。
使われ方：有限生成イデアルで定まる閉台と係数つき perfect 対象の台条件の同定。 -/
theorem centralSupport_iff_power_annihilation {ι : Type*} [Finite ι] (z : ι → R)
    {E : ι → Type w} [∀ i, Category.{t} (E i)] [∀ i, Preadditive (E i)]
    [∀ i, Linear R (E i)] (loc : ∀ i, C ⥤ E i)
    [∀ i, (loc i).Additive] [∀ i, (loc i).Linear R]
    [∀ i, IsLocalizedModule (Submonoid.powers (z i))
      ((loc i).mapLinearMap R : (P ⟶ P) →ₗ[R] _)] :
    (∀ i, IsZero ((loc i).obj P)) ↔ ∃ n : ℕ, ∀ i, z i ^ n • (𝟙 P) = 0 := by
  rw [← central_finite_power_annihilation P z]
  exact forall_congr' fun i ↦ centralLocalization_isZero_iff (loc i) (z i) P

omit F in
/-- 概要：有限生成中心イデアルの各元の冪ねじれはイデアル冪による恒等射の消滅と同値（(3.6)）。
方針：恒等射の張る巡回加群の零化イデアルに移し、根基包含から冪包含を得る。
規約：係数圏の自己準同型環の可換性は不要。中心作用の環 R のみ可換とする。
使われ方：中心局所化の台条件とイデアル冪ねじれ条件の比較。 -/
theorem central_ideal_power_annihilation_iff (J : Ideal R) (hJ : J.FG) :
    (∀ z ∈ J, ∃ n : ℕ, z ^ n • (𝟙 P) = 0) ↔
      ∃ n : ℕ, ∀ z ∈ J ^ n, z • (𝟙 P) = 0 := by
  let I := (Submodule.span R ({𝟙 P} : Set (P ⟶ P))).annihilator
  have memI (z : R) : z ∈ I ↔ z • (𝟙 P) = 0 :=
    Submodule.mem_annihilator_span_singleton (𝟙 P) z
  constructor
  · intro h
    have hr : J ≤ I.radical := by
      intro z hz
      obtain ⟨n, hn⟩ := h z hz
      exact ⟨n, (memI _).mpr hn⟩
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hr hJ
    exact ⟨n, fun z hz ↦ (memI z).mp (hn hz)⟩
  · rintro ⟨n, hn⟩ z hz
    exact ⟨n, hn (z ^ n) (Ideal.pow_mem_pow hz n)⟩

end SerrePositivity.KST.Descent

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Paper "Proof step §3.1 support" (partial := stronger-hyp) "仮定：有限個の中心スカラーと対象。各局所化関手が自己準同型加群のスカラー局所化を与えると仮定（Lean が強い：加群上の局所化模型を明示）。結論：各局所化で対象が零であることと、一様な冪が恒等射を殺すことの同値（同じ判定）。"] _root_.SerrePositivity.KST.Descent.centralSupport_iff_power_annihilation
attribute [cite Paper "Proof step §4.5 support" (partial := stronger-hyp) "仮定：有限個の中心スカラーと対象。各局所化関手が自己準同型加群のスカラー局所化を与えると仮定（Lean が強い：加群上の局所化模型を明示）。結論：局所化で消える条件と恒等射の一様冪零の同値（同じ支持条件。4.6 の圏同値は含まない）。"] _root_.SerrePositivity.KST.Descent.centralSupport_iff_power_annihilation
