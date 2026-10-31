module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import SerrePositivity.CategoryTheory.AlternatingSum
public import SerrePositivity.CategoryTheory.Abelian.ShortComplex
public import SerrePositivity.CategoryTheory.TriangulatedK0
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Data.Int.Interval

/-! # ホモロジー関手による Euler 評価と比較

## 概要

有界なホモロジー関手による Euler 評価を K₀ 上の準同型として定め、長完全列での加法性を示す。二つのホモロジー的 Euler 評価の対称な比較（群の軌道和の一致）を与える。

## 方針

加法性は長完全列の交代和の添字の付け替え（`AlternatingSum`）による。比較は、G 不変元の正の倍が基底からの像に入るとき軌道和が一致する、という補題（`orbitSum_eq_of_descent`）に帰着する。

## 規約

Euler 評価 `homologicalEuler`・`homologicalEulerK0` と長完全列の加法性は、値を任意の加法群 `M` に取る（符号は `zsmul`）。実数値で項を比べる側は `zsmul_eq_mul` で積の形に直す。群の軌道和の比較は実数値のまま。評価の定義域を `IsSerreClass` な部分圏上の関数にする一般化は、G₀ を扱う区切り 1-4（KTheory）で行う。

## 使われ方

LengthAlgebra の比較、Paper の Thm 4.7 と第二の比較、Asymptotic の Euler 評価、KTheory の Euler。
-/

@[expose] public noncomputable section

section ConjugateSumPart

namespace SerrePositivity

/-- **共役和の一致**：`φ ∘ f = ψ ∘ f`（`h1`）かつ `G` 不変な元の正の倍数が `f` の像に入る（`h2`）なら、
任意の `y` で `Σ_g φ(g • y) = Σ_g ψ(g • y)`。 -/
theorem orbitSum_eq_of_descent {K K' : Type*} [AddCommGroup K] [AddCommGroup K'] (f : K →+ K')
    {G : Type*} [Group G] [Fintype G] [DistribMulAction G K']
    (φ ψ : K' →+ ℝ) (h1 : ∀ x, φ (f x) = ψ (f x))
    (h2 : ∀ y : K', (∀ g : G, g • y = y) → ∃ (n : ℕ) (x : K), 0 < n ∧ n • y = f x)
    (y : K') : ∑ g : G, φ (g • y) = ∑ g : G, ψ (g • y) := by
  set s := ∑ g : G, g • y with hs
  have hinv : ∀ h : G, h • s = s := by
    intro h
    rw [hs, Finset.smul_sum]
    simp_rw [smul_smul]
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g ↦ rfl)
  obtain ⟨n, x, hn, hx⟩ := h2 s hinv
  have hφ : (n : ℝ) * ∑ g : G, φ (g • y) = φ (f x) := by
    rw [← hx, map_nsmul, nsmul_eq_mul, hs, map_sum]
  have hψ : (n : ℝ) * ∑ g : G, ψ (g • y) = ψ (f x) := by
    rw [← hx, map_nsmul, nsmul_eq_mul, hs, map_sum]
  have : (n : ℝ) * ∑ g : G, φ (g • y) = (n : ℝ) * ∑ g : G, ψ (g • y) := by
    rw [hφ, hψ, h1]
  exact mul_left_cancel₀ (by exact_mod_cast hn.ne') this

/-- **基底公式つきの共役和の一致**：二つの評価が `f` に沿って共通の関数 `χA : K → ℝ` の定数倍に分解する
（`φ (f x) = e₁ * χA x`、`ψ (f x) = e₂ * χA x`、基底公式）とき、`e₁ = e₂` なら `orbitSum_eq_of_descent` の仮定 `h1`
が成り立ち、降下 `h2` から共役和が一致する。二つの実現の比較定理はこの形で使う
（解説の系「基底公式つきの共役和比較」）。 -/
theorem conjSum_eq_of_base_formula {K K' : Type*} [AddCommGroup K] [AddCommGroup K']
    (f : K →+ K') {G : Type*} [Group G] [Fintype G] [DistribMulAction G K']
    (φ ψ : K' →+ ℝ) (χA : K → ℝ) (e₁ e₂ : ℝ)
    (h₁ : ∀ x, φ (f x) = e₁ * χA x) (h₂ : ∀ x, ψ (f x) = e₂ * χA x) (he : e₁ = e₂)
    (h2 : ∀ y : K', (∀ g : G, g • y = y) → ∃ (n : ℕ) (x : K), 0 < n ∧ n • y = f x)
    (y : K') : ∑ g : G, φ (g • y) = ∑ g : G, ψ (g • y) :=
  orbitSum_eq_of_descent f φ ψ (fun x ↦ by rw [h₁, h₂, he]) h2 y

end SerrePositivity


end ConjugateSumPart

section ExactSequenceEulerPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {A : Type*} [Category* A] [Abelian A] {M : Type*} [AddCommGroup M] (l : A → M)
  (hi : ∀ {X Y : A}, (X ≅ Y) → l X = l Y)
  (ha : ∀ {S : ShortComplex A}, S.ShortExact → l S.X₂ = l S.X₁ + l S.X₃)

include hi ha in
/-- 完全列の中央の評価は両側の射の像の評価の和である。 -/
lemma additiveLength_exact_images {S : ShortComplex A} (hS : S.Exact) :
    l S.X₂ = l (Abelian.image S.f) + l (Abelian.image S.g) := by
  have h := ha (imageCoimageShortComplex_shortExact hS)
  change l S.X₂ = l (Abelian.image S.f) + l (Abelian.coimage S.g) at h
  rw [hi (Abelian.coimageIsoImage S.g)] at h
  exact h

include hi ha in
/-- 長完全列の Euler 加法性。第二・第三の対象列の有界性だけで十分であり、
射影性・長さの正値性・三角圏から来ることは仮定しない。 -/
lemma additiveLength_euler_exact_sequence
    (hz : ∀ X : A, IsZero X → l X = 0)
    (X₁ X₂ X₃ : ℤ → A)
    (α : ∀ i, X₁ i ⟶ X₂ i) (β : ∀ i, X₂ i ⟶ X₃ i)
    (δ : ∀ i, X₃ i ⟶ X₁ (i + 1))
    {w₂ : ∀ i, α i ≫ β i = 0} {w₃ : ∀ i, β i ≫ δ i = 0}
    {w₁ : ∀ i, δ i ≫ α (i + 1) = 0}
    (h₂ : ∀ i, (ShortComplex.mk (α i) (β i) (w₂ i)).Exact)
    (h₃ : ∀ i, (ShortComplex.mk (β i) (δ i) (w₃ i)).Exact)
    (h₁ : ∀ i, (ShortComplex.mk (δ i) (α (i + 1)) (w₁ i)).Exact)
    (hb₂ : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (X₂ i))
    (hb₃ : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (X₃ i)) :
    (∑ᶠ i : ℤ, (i.negOnePow : ℤ) • l (X₂ i)) =
      (∑ᶠ i : ℤ, (i.negOnePow : ℤ) • l (X₁ i)) +
        ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • l (X₃ i) := by
  let a := fun i ↦ l (Abelian.image (α i))
  let b := fun i ↦ l (Abelian.image (β i))
  let d := fun i ↦ l (Abelian.image (δ i))
  have hfa : Function.HasFiniteSupport a := by
    obtain ⟨p, q, hpq⟩ := hb₂
    apply finiteSupport_of_bounded_zero a p q
    intro i hi
    exact hz _ (IsZero.of_mono (Abelian.image.ι (α i)) (hpq i hi))
  have hfb : Function.HasFiniteSupport b := by
    obtain ⟨p, q, hpq⟩ := hb₃
    apply finiteSupport_of_bounded_zero b p q
    intro i hi
    exact hz _ (IsZero.of_mono (Abelian.image.ι (β i)) (hpq i hi))
  have hfd : Function.HasFiniteSupport d := by
    obtain ⟨p, q, hpq⟩ := hb₃
    apply finiteSupport_of_bounded_zero d p q
    intro i hi
    exact hz _ (IsZero.of_epi (Abelian.factorThruImage (δ i)) (hpq i hi))
  have h₂ (i : ℤ) : l (X₂ i) = a i + b i :=
    additiveLength_exact_images l hi ha (h₂ i)
  have h₃ (i : ℤ) : l (X₃ i) = b i + d i :=
    additiveLength_exact_images l hi ha (h₃ i)
  have h₁ (i : ℤ) : l (X₁ i) = d (i - 1) + a i := by
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
    rw [add_sub_cancel_right]
    exact additiveLength_exact_images l hi ha (h₁ j)
  simp_rw [h₂, h₁, h₃]
  exact alternatingGroupFinsum_exact a b d hfa hfb hfd

end SerrePositivity

end ExactSequenceEulerPart

section HomologicalEulerPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped BigOperators

variable {A : Type*} [Category* A] [Abelian A] {M : Type*} [AddCommGroup M] (l : A → M)
  (hi : ∀ {X Y : A}, (X ≅ Y) → l X = l Y)
  (ha : ∀ {S : ShortComplex A}, S.ShortExact → l S.X₂ = l S.X₁ + l S.X₃)

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]

/-- ホモロジー関手とアーベル圏上の評価から定める Euler 和。 -/
noncomputable def homologicalEuler (X : C) : M :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • l ((F.shift i).obj X)

include hi in
omit [Abelian A] [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [F.IsHomological] in
/-- Euler 和は対象の同型で不変である。 -/
lemma homologicalEuler_iso {X Y : C} (e : X ≅ Y) :
    homologicalEuler l F X = homologicalEuler l F Y := by
  unfold homologicalEuler
  congr 1
  funext i
  rw [hi ((F.shift i).mapIso e)]

variable (hz : ∀ X : A, IsZero X → l X = 0)
  (hb : ∀ X : C, ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((F.shift i).obj X))

include hz hb in
omit [Abelian A] [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [F.IsHomological] in
/-- 有界なホモロジー評価の交代和は有限支持である。 -/
lemma homologicalEuler_hasFiniteSupport (X : C) :
    Function.HasFiniteSupport (fun i : ℤ ↦ (i.negOnePow : ℤ) • l ((F.shift i).obj X)) := by
  obtain ⟨a, b, hab⟩ := hb X
  apply finiteSupport_of_bounded_zero _ a b
  intro i hi
  simp only [hz _ (hab i hi), smul_zero]

include hi ha hz hb in
/-- 有界なホモロジー関手の Euler 和は完全三角形で加法的である。 -/
lemma homologicalEuler_triangle (T : Triangle C) (hT : T ∈ distTriang C) :
    homologicalEuler l F T.obj₂ = homologicalEuler l F T.obj₁ + homologicalEuler l F T.obj₃ := by
  exact additiveLength_euler_exact_sequence l hi ha hz
    (fun i ↦ (F.shift i).obj T.obj₁) (fun i ↦ (F.shift i).obj T.obj₂)
    (fun i ↦ (F.shift i).obj T.obj₃) (fun i ↦ (F.shift i).map T.mor₁)
    (fun i ↦ (F.shift i).map T.mor₂) (fun i ↦ F.homologySequenceδ T i (i + 1) rfl)
    (fun i ↦ F.homologySequence_exact₂ T hT i)
    (fun i ↦ F.homologySequence_exact₃ T hT i (i + 1) rfl)
    (fun i ↦ F.homologySequence_exact₁ T hT i (i + 1) rfl) (hb T.obj₂) (hb T.obj₃)

/-- 有界なホモロジー関手の Euler 評価が与える `K₀` 上の準同型。 -/
noncomputable def homologicalEulerK0 : TriangulatedK0 C →+ M :=
  TriangulatedK0.lift (homologicalEuler l F) (homologicalEuler_iso l hi F)
    (homologicalEuler_triangle l hi ha F hz hb)

/-- Grothendieck 類上の評価は元の Euler 和で計算できる。 -/
@[simp] lemma homologicalEulerK0_mk (X : C) :
    homologicalEulerK0 l hi ha F hz hb (TriangulatedK0.mk X) = homologicalEuler l F X :=
  TriangulatedK0.lift_mk ..

include hz in
omit [Abelian A] [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [F.IsHomological] in
/-- ホモロジーが第零次に集中すれば、Euler 評価はその長さに等しい。 -/
lemma homologicalEuler_eq_length_zero (X : C)
    (h : ∀ q : ℤ, q ≠ 0 → IsZero ((F.shift q).obj X)) :
    homologicalEuler l F X = l ((F.shift (0 : ℤ)).obj X) := by
  rw [homologicalEuler, finsum_eq_single _ (0 : ℤ)]
  · simp
  · intro q hq
    rw [hz _ (h q hq), smul_zero]

include hi in
omit [Abelian A] [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [F.IsHomological] in
/-- 各次数の評価関手の自然同型は Euler 評価を保つ。 -/
lemma homologicalEuler_natIso (F' : C ⥤ A) [F'.ShiftSequence ℤ]
    (e : ∀ q : ℤ, F.shift q ≅ F'.shift q) (X : C) :
    homologicalEuler l F X = homologicalEuler l F' X := by
  unfold homologicalEuler
  congr 1
  funext q
  rw [hi ((e q).app X)]

/-- 対象上の計算式による Euler 準同型の一意性。 -/
lemma homologicalEulerK0_unique (φ : TriangulatedK0 C →+ M)
    (h : ∀ X, φ (TriangulatedK0.mk X) = homologicalEuler l F X) :
    φ = homologicalEulerK0 l hi ha F hz hb := by
  apply TriangulatedK0.hom_ext
  intro X
  simpa using h X

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (T : D ⥤ C) [T.CommShift ℤ] [T.IsTriangulated]
  (G : D ⥤ A) [G.IsHomological] [G.ShiftSequence ℤ]
  (hbG : ∀ X : D, ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((G.shift i).obj X))

/-- 三角関手による引き戻しは、各次数の自然同型から Euler 評価の引き戻しを与える。 -/
lemma homologicalEulerK0_pullback
    (e : ∀ q : ℤ, T ⋙ F.shift q ≅ G.shift q) :
    (homologicalEulerK0 l hi ha F hz hb).comp (TriangulatedK0.map T) =
      homologicalEulerK0 l hi ha G hz hbG := by
  apply TriangulatedK0.hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, TriangulatedK0.map_mk, homologicalEulerK0_mk]
  unfold homologicalEuler
  congr 1
  funext q
  rw [show l ((F.shift q).obj (T.obj X)) = l ((G.shift q).obj X) from hi ((e q).app X)]

end SerrePositivity

end HomologicalEulerPart

section EulerComparisonPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
  (l₁ : A → ℝ)
  (hi₁ : ∀ {X Y : A}, (X ≅ Y) → l₁ X = l₁ Y)
  (ha₁ : ∀ {S : ShortComplex A}, S.ShortExact → l₁ S.X₂ = l₁ S.X₁ + l₁ S.X₃)
  (hz₁ : ∀ X, IsZero X → l₁ X = 0)
  (l₂ : B → ℝ)
  (hi₂ : ∀ {X Y : B}, (X ≅ Y) → l₂ X = l₂ Y)
  (ha₂ : ∀ {S : ShortComplex B}, S.ShortExact → l₂ S.X₂ = l₂ S.X₁ + l₂ S.X₃)
  (hz₂ : ∀ X, IsZero X → l₂ X = 0)

section SameCategory

variable (F₁ : C ⥤ A) [F₁.IsHomological] [F₁.ShiftSequence ℤ]
  (hb₁ : ∀ X : C, ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((F₁.shift q).obj X))
  (F₂ : C ⥤ B) [F₂.IsHomological] [F₂.ShiftSequence ℤ]
  (hb₂ : ∀ X : C, ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((F₂.shift q).obj X))

/-- 基底からの一致と不変類の降下による、二つの Euler 評価の共役和の一致。 -/
theorem homologicalEulerK0_conjSum_eq
    {K : Type*} [AddCommGroup K] (f : K →+ TriangulatedK0 C)
    {G : Type*} [Group G] [Fintype G] [DistribMulAction G (TriangulatedK0 C)]
    (hbase : ∀ x,
      homologicalEulerK0 l₁ hi₁ ha₁ F₁ hz₁ hb₁ (f x) =
        homologicalEulerK0 l₂ hi₂ ha₂ F₂ hz₂ hb₂ (f x))
    (hdesc : ∀ y : TriangulatedK0 C, (∀ g : G, g • y = y) →
      ∃ (n : ℕ) (x : K), 0 < n ∧ n • y = f x)
    (y : TriangulatedK0 C) :
    ∑ g : G, homologicalEulerK0 l₁ hi₁ ha₁ F₁ hz₁ hb₁ (g • y) =
      ∑ g : G, homologicalEulerK0 l₂ hi₂ ha₂ F₂ hz₂ hb₂ (g • y) :=
  orbitSum_eq_of_descent f _ _ hbase hdesc y

end SameCategory

section Pullback

variable {C₁ : Type*} [Category* C₁] [Preadditive C₁] [HasZeroObject C₁] [HasShift C₁ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [Pretriangulated C₁]
  {C₂ : Type*} [Category* C₂] [Preadditive C₂] [HasZeroObject C₂] [HasShift C₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₂ n).Additive] [Pretriangulated C₂]
  (F₁ : C₁ ⥤ A) [F₁.IsHomological] [F₁.ShiftSequence ℤ]
  (hb₁ : ∀ X : C₁, ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((F₁.shift q).obj X))
  (F₂ : C₂ ⥤ B) [F₂.IsHomological] [F₂.ShiftSequence ℤ]
  (hb₂ : ∀ X : C₂, ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((F₂.shift q).obj X))

/-- **基底公式つきの共役和比較（引き戻した Euler 評価）**：評価元 `C` の `K₀` に有限群 `G` が作用し、
二つの評価 `χᵢ = (C_i 上の Euler 評価) ∘ uᵢ` が、基底 `K` からの写像 `f` に沿って共通の `χA` の定数倍
`eᵢ * χA` に等しい（基底公式）とする。`e₁ = e₂` と不変類の降下から、全ての類で共役和が一致する。
評価先 `A`、`B` を同じ圏に同定する必要も、`uᵢ` の同変性も要らない。 -/
theorem homologicalEulerK0_pullback_conjSum_eq_of_base_formula
    (u₁ : TriangulatedK0 C →+ TriangulatedK0 C₁) (u₂ : TriangulatedK0 C →+ TriangulatedK0 C₂)
    {K : Type*} [AddCommGroup K] (f : K →+ TriangulatedK0 C)
    {G : Type*} [Group G] [Fintype G] [DistribMulAction G (TriangulatedK0 C)]
    (χA : K → ℝ) (e₁ e₂ : ℝ)
    (h₁ : ∀ x, ((homologicalEulerK0 l₁ hi₁ ha₁ F₁ hz₁ hb₁).comp u₁) (f x) = e₁ * χA x)
    (h₂ : ∀ x, ((homologicalEulerK0 l₂ hi₂ ha₂ F₂ hz₂ hb₂).comp u₂) (f x) = e₂ * χA x)
    (he : e₁ = e₂)
    (hdesc : ∀ y : TriangulatedK0 C, (∀ g : G, g • y = y) →
      ∃ (n : ℕ) (x : K), 0 < n ∧ n • y = f x)
    (y : TriangulatedK0 C) :
    ∑ g : G, ((homologicalEulerK0 l₁ hi₁ ha₁ F₁ hz₁ hb₁).comp u₁) (g • y) =
      ∑ g : G, ((homologicalEulerK0 l₂ hi₂ ha₂ F₂ hz₂ hb₂).comp u₂) (g • y) :=
  conjSum_eq_of_base_formula f _ _ χA e₁ e₂ h₁ h₂ he hdesc y

end Pullback

end SerrePositivity

end EulerComparisonPart
