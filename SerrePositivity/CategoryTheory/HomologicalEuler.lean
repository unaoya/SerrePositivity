module

public import SerrePositivity.CategoryTheory.ExactSequenceEuler
public import SerrePositivity.CategoryTheory.TriangulatedK0
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval

/-!
# 有界なホモロジー関手による Euler 評価

アーベル圏上の同型不変・短完全列で加法的な実数値の評価を、
有界なホモロジー関手の交代和として三角圏の対象に適用する。
長完全列を像の短完全列に分け、有限支持の交代和を取ると三角加法性が得られる。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped BigOperators

variable {A : Type*} [Category* A] [Abelian A] (l : A → ℝ)
  (hi : ∀ {X Y : A}, (X ≅ Y) → l X = l Y)
  (ha : ∀ {S : ShortComplex A}, S.ShortExact → l S.X₂ = l S.X₁ + l S.X₃)


variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]

/-- ホモロジー関手とアーベル圏上の評価から定める Euler 和。 -/
noncomputable def homologicalEuler (X : C) : ℝ :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * l ((F.shift i).obj X)

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
    Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * l ((F.shift i).obj X)) := by
  obtain ⟨a, b, hab⟩ := hb X
  apply (Set.finite_Icc a b).subset
  intro i hi
  by_contra hn
  exact hi (by simp only [hz _ (hab i (by simp only [Set.mem_Icc] at hn; omega)), mul_zero])

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
noncomputable def homologicalEulerK0 : TriangulatedK0 C →+ ℝ :=
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
    rw [hz _ (h q hq), mul_zero]

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
lemma homologicalEulerK0_unique (φ : TriangulatedK0 C →+ ℝ)
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
