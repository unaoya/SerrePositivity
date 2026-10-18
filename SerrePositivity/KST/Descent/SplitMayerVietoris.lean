module

public import SerrePositivity.KST.Descent.MayerVietoris
public import Mathlib.LinearAlgebra.Prod

/-!
# 軌道正方形の比較元となる分裂長完全列

## 概要
`A → A × C → C` を `a ↦ (a, r a)`、`(a,c) ↦ r a - c` として全次数で構成する。
この列から実際の長完全列への比較では、境界の可換性も制限の差の全射性から得られる。

## 方針
指定した写像で三箇所の完全性を直接証明する。
境界の自然性を仮定せず、比較先の完全性と制限の差の全射性で証明する。

## 規約
任意の抽象 blowup に零の境界を仮定するものではない。
比較元の恒等的な正方形の境界だけが零である。

## 使われ方
論文 定理 3.1 の軌道正方形に (3.8) と中心上の帰納仮定を適用する際の比較元。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity.KST.Descent

/-- 概要：恒等的な正方形の二つの部分への制限（論文 定理 3.1 の比較元）。
方針：元とその制限の組を取る。
規約：第一成分は恒等写像、第二成分は与えた r。
使われ方：軌道正方形に比較する分裂長完全列。 -/
def splitRestriction {A C : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup C] [Module ℚ C] (r : A →ₗ[ℚ] C) : A →ₗ[ℚ] A × C :=
  LinearMap.id.prod r

/-- 概要：恒等的な正方形の制限の差（論文 定理 3.1 の比較元）。
方針：第一成分の r による制限から第二成分を引く。
規約：`SquareSequence` と同じ符号。
使われ方：境界が零の分裂列の第二の射。 -/
def splitDifference {A C : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup C] [Module ℚ C] (r : A →ₗ[ℚ] C) : A × C →ₗ[ℚ] C :=
  r.comp (LinearMap.fst ℚ A C) - LinearMap.snd ℚ A C

/-- 概要：比較元の制限の差は全射（論文 定理 3.1）。
方針：c の原像として `(0,-c)` を取る。
規約：r の全射性は不要。
使われ方：比較先の長完全列における境界の可換性を証明する。 -/
theorem splitDifference_surjective {A C : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup C] [Module ℚ C] (r : A →ₗ[ℚ] C) : Function.Surjective (splitDifference r) := by
  intro c
  refine ⟨(0, -c), ?_⟩
  change r 0 - -c = c
  simp only [map_zero, neg_neg, zero_sub]

/-- 概要：恒等的な正方形の全整数次数の分裂長完全列（論文 定理 3.1）。
方針：制限は `(id,r)`、差は `r - id`、境界は零とし、完全性を直接確認する。
規約：この境界の零性は比較元の特別な正方形の性質。
使われ方：(3.8) と中心上の帰納仮定による軌道正方形の比較。 -/
def splitMayerVietoris (A C : ℤ → ModuleCat.{u} ℚ) (r : ∀ n, A n →ₗ[ℚ] C n) :
    GradedMayerVietoris.{u} where
  A := A
  B n := ModuleCat.of ℚ (A n × C n)
  C := C
  restriction n := splitRestriction (r n)
  difference n := splitDifference (r n)
  boundary _ := 0
  exact_boundary_restriction n := by
    intro x
    constructor
    · intro h
      have hx := congrArg Prod.fst h
      change x = 0 at hx
      exact ⟨0, hx.symm⟩
    · rintro ⟨_, rfl⟩
      exact map_zero _
  exact_restriction_difference n := by
    intro x
    constructor
    · intro h
      change r n x.1 - x.2 = 0 at h
      exact ⟨x.1, Prod.ext rfl (sub_eq_zero.mp h)⟩
    · rintro ⟨a, rfl⟩
      exact sub_self _
  exact_difference_boundary n := by
    intro c
    exact ⟨fun _ ↦ splitDifference_surjective (r (n + 1)) c, fun _ ↦ rfl⟩

/-- 概要：分裂列から長完全列への比較では境界との可換性も導ける（論文 定理 3.1）。
方針：制限の差の全射性で元を持ち上げ、比較先の差と境界の零合成を使う。
規約：比較先全体の境界を零と仮定せず、指定比較の像での可換性を証明する。
使われ方：軌道正方形の比較を境界に自然な五項補題の入力にする。 -/
def splitMayerVietorisComparison (A C : ℤ → ModuleCat.{u} ℚ) (r : ∀ n, A n →ₗ[ℚ] C n)
    (T : GradedMayerVietoris.{u})
    (a : ∀ n, A n →ₗ[ℚ] T.A n) (b : ∀ n, A n × C n →ₗ[ℚ] T.B n)
    (c : ∀ n, C n →ₗ[ℚ] T.C n)
    (restriction_naturality : ∀ n, (T.restriction n).comp (a n) =
      (b n).comp (splitRestriction (r n)))
    (difference_naturality : ∀ n, (T.difference n).comp (b n) =
      (c n).comp (splitDifference (r n))) :
    GradedMayerVietoris.Hom (splitMayerVietoris A C r) T where
  mapA := a
  mapB := b
  mapC := c
  comm_restriction := restriction_naturality
  comm_difference := difference_naturality
  comm_boundary n := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, hz⟩ := splitDifference_surjective (r (n + 1)) x
    have h := LinearMap.congr_fun (difference_naturality (n + 1)) z
    change T.difference (n + 1) (b (n + 1) z) = c (n + 1) (splitDifference (r (n + 1)) z) at h
    change T.boundary n (c (n + 1) x) = a n 0
    rw [map_zero, ← hz, ← h]
    exact (T.exact_difference_boundary n).apply_apply_eq_zero (b (n + 1) z)

/-- 概要：分裂列の二つの部分の比較が全次数同型なら元の比較も同型（論文 定理 3.1）。
方針：境界に自然な比較を制限の可換式から構成し、全次数の五項補題を適用する。
規約：a 自体の同型性や境界の可換性を仮定していない。
使われ方：(3.8) と中心上の帰納仮定から元の軌道比較を得る代数的な貼り合わせ。 -/
theorem splitMayerVietorisComparison_bijective
    (A C : ℤ → ModuleCat.{u} ℚ) (r : ∀ n, A n →ₗ[ℚ] C n) (T : GradedMayerVietoris.{u})
    (a : ∀ n, A n →ₗ[ℚ] T.A n) (b : ∀ n, A n × C n →ₗ[ℚ] T.B n)
    (c : ∀ n, C n →ₗ[ℚ] T.C n)
    (restriction_naturality : ∀ n, (T.restriction n).comp (a n) =
      (b n).comp (splitRestriction (r n)))
    (difference_naturality : ∀ n, (T.difference n).comp (b n) =
      (c n).comp (splitDifference (r n)))
    (hb : ∀ n, Function.Bijective (b n)) (hc : ∀ n, Function.Bijective (c n)) (n : ℤ) :
    Function.Bijective (a n) :=
  GradedMayerVietoris.Hom.bijective_mapA
    (splitMayerVietorisComparison A C r T a b c
      restriction_naturality difference_naturality) hb hc n

end SerrePositivity.KST.Descent
