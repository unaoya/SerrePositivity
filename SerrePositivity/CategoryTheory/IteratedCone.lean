module

public import SerrePositivity.CategoryTheory.Euler
public import SerrePositivity.CategoryTheory.ScalarSupport
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Data.Nat.Choose.Sum
public import SerrePositivity.CategoryTheory.Abelian.SerreLength
public import Mathlib.Algebra.FiniteSupport.Basic

/-! # 反復錐の長さと消去

## 概要

零写像の錐のホモロジーの長さ、反復錐の分裂と新しい交叉型の消滅、零写像の錐では消去スカラーの指数を増やさなくてよいこと、錐の長さの漸化式の二項展開、上に有界な係数列に対する反復錐の消去を与える。

## 方針

反復錐を分裂する三角形の列として書き、長さの漸化式を二項係数で解く。

## 規約

長さは加法的な長さ（`Abelian/SerreLength`）。二項展開の部分は ℤ → ℝ の計算で圏論を使わない。

## 使われ方

Asymptotic の Koszul の評価、LengthAlgebra・PerfectComplex の Koszul の長さ。
-/

@[expose] public noncomputable section

section HomologicalConeLengthPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {A : Type*} [Category* A] [Abelian A]
  (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]

/-- 第一射が零の完全三角形から得られるホモロジー短完全列。 -/
lemma homologySequence_shortExact_of_zero (T : Triangle C) (hT : T ∈ distTriang C)
    (hf : T.mor₁ = 0) (q : ℤ) :
    (ShortComplex.mk _ _ (F.comp_homologySequenceδ T hT q (q + 1) rfl)).ShortExact := by
  have hm : Mono ((F.shift q).map T.mor₂) :=
    (F.homologySequence_mono_shift_map_mor₂_iff T hT q).mpr (by rw [hf, Functor.map_zero])
  have he : Epi (F.homologySequenceδ T q (q + 1) rfl) :=
    (F.homologySequence_exact₁ T hT q (q + 1) rfl).epi_f_iff.mpr
      (by change (F.shift (q + 1)).map T.mor₁ = 0; rw [hf, Functor.map_zero])
  exact ⟨F.homologySequence_exact₃ T hT q (q + 1) rfl⟩

variable (l : A → ℝ)
  (ha : ∀ {S : ShortComplex A}, S.ShortExact → l S.X₂ = l S.X₁ + l S.X₃)

include ha in
/-- 零写像の錐の長さは、隣接する二次数の長さの和。 -/
lemma homologyLength_zero_cone (T : Triangle C) (hT : T ∈ distTriang C)
    (hf : T.mor₁ = 0) (q : ℤ) :
    l ((F.shift q).obj T.obj₃) =
      l ((F.shift q).obj T.obj₂) + l ((F.shift (q + 1)).obj T.obj₁) :=
  ha (homologySequence_shortExact_of_zero F T hT hf q)

end SerrePositivity

end HomologicalConeLengthPart

section ScalarZeroConePart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C]
  [Linear R C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C]

/-- 第一射が零で、スカラーが両端で零なら、錐でも同じスカラーが零。 -/
lemma scalar_zero_on_zero_cone (T : Triangle C) (hT : T ∈ distTriang C)
    (hf : T.mor₁ = 0) (a : R)
    (h₁ : a • 𝟙 T.obj₁ = 0) (h₂ : a • 𝟙 T.obj₂ = 0) :
    a • 𝟙 T.obj₃ = 0 := by
  obtain ⟨e, _⟩ := exists_iso_binaryBiproduct_of_distTriang T.rotate
    (rot_of_distTriang T hT) (by
      change -T.mor₁⟦(1 : ℤ)⟧' = 0
      rw [hf, Functor.map_zero, neg_zero])
  change T.obj₃ ≅ T.obj₂ ⊞ T.obj₁⟦(1 : ℤ)⟧ at e
  have h₁' : a • 𝟙 (T.obj₁⟦(1 : ℤ)⟧) = 0 := by
    have h := congrArg (shiftFunctor C (1 : ℤ)).map h₁
    rw [Functor.map_smul, (shiftFunctor C (1 : ℤ)).map_id, Functor.map_zero] at h
    exact h
  have hb : a • 𝟙 (T.obj₂ ⊞ T.obj₁⟦(1 : ℤ)⟧) = 0 := by
    apply biprod.hom_ext
    · calc
        _ = biprod.fst ≫ (a • 𝟙 T.obj₂) := by simp
        _ = _ := by rw [h₂]; simp
    · calc
        _ = biprod.snd ≫ (a • 𝟙 (T.obj₁⟦(1 : ℤ)⟧)) := by simp
        _ = _ := by rw [h₁']; simp
  apply (cancel_mono e.hom).mp
  calc
    _ = e.hom ≫ (a • 𝟙 _) := by simp
    _ = _ := by rw [hb]; simp

end SerrePositivity

end ScalarZeroConePart

section ConeLengthBinomialPart

namespace SerrePositivity

open scoped BigOperators

/-- cochain の次数を一つ進める線形作用素。 -/
def cochainLengthShift : Module.End ℝ (ℤ → ℝ) where
  toFun f q := f (q + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma cochainLengthShift_apply (f : ℤ → ℝ) (q : ℤ) :
    cochainLengthShift f q = f (q + 1) := rfl

@[simp] lemma cochainLengthShift_pow_apply (n : ℕ) (f : ℤ → ℝ) (q : ℤ) :
    (cochainLengthShift ^ n) f q = f (q + n) := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, cochainLengthShift_apply, ih]
      congr 1
      omega

/-- 零写像の錐を e 回取る漸化式の二項係数による展開。 -/
lemma coneLength_binomial (n : ℕ) (f : ℤ → ℝ) (q : ℤ) :
    ((cochainLengthShift + 1) ^ n) f q =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * f (q + j) := by
  rw [(Commute.one_right cochainLengthShift).add_pow]
  simp only [one_pow, mul_one, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply, Module.End.natCast_apply,
    cochainLengthShift_pow_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]

/-- 錐の漸化式は、次数移動作用素の冪と一致する。 -/
lemma coneLength_pow_of_recurrence (b : ℕ → ℤ → ℝ) (n : ℕ)
    (hb : ∀ k < n, ∀ q, b (k + 1) q = b k q + b k (q + 1)) :
    b n = ((cochainLengthShift + 1) ^ n) (b 0) := by
  have hi : ∀ k ≤ n, b k = ((cochainLengthShift + 1) ^ k) (b 0) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ← ih (by omega)]
        funext q
        simpa only [LinearMap.add_apply, cochainLengthShift_apply, Module.End.one_apply,
          Pi.add_apply, add_comm] using hb k (by omega) q
  exact hi n le_rfl

/-- 各段が錐の漸化式を満たせば、最後の係数は二項公式で与えられる。 -/
lemma coneLength_binomial_of_recurrence (b : ℕ → ℤ → ℝ) (n : ℕ)
    (hb : ∀ k < n, ∀ q, b (k + 1) q = b k q + b k (q + 1)) (q : ℤ) :
    b n q = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * b 0 (q + j) := by
  rw [coneLength_pow_of_recurrence b n hb]
  exact coneLength_binomial n (b 0) q

/-- homological 添字では右辺は i-j となり、(1+t)^n の係数と一致する。 -/
lemma coneLength_binomial_homological (b : ℕ → ℤ → ℝ) (n : ℕ)
    (hb : ∀ k < n, ∀ q, b (k + 1) q = b k q + b k (q + 1)) (i : ℤ) :
    b n (-i) = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * b 0 (-(i - j)) := by
  simpa only [neg_sub, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm] using
    coneLength_binomial_of_recurrence b n hb (-i)

end SerrePositivity

end ConeLengthBinomialPart

section IteratedConePart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped BigOperators

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- 零射の反復錐の分裂を表す再帰的な直和。 -/
noncomputable def iteratedZeroCone (X : C) : ℕ → C
  | 0 => X
  | n + 1 => iteratedZeroCone X n ⊞ (iteratedZeroCone X n)⟦(1 : ℤ)⟧

variable (X : ℕ → C) (ι : ∀ k, X k ⟶ X (k + 1))
  (π : ∀ k, X (k + 1) ⟶ (X k)⟦(1 : ℤ)⟧) (n : ℕ)
  (hT : ∀ k < n, Triangle.mk (0 : X k ⟶ X k) (ι k) (π k) ∈ distTriang C)

include hT in
/-- 零射の錐の列は、シフトと二項直和だけで表される。 -/
lemma iteratedZeroCone_iso : Nonempty (X n ≅ iteratedZeroCone (X 0) n) := by
  induction n with
  | zero => exact ⟨Iso.refl _⟩
  | succ n ih =>
      obtain ⟨e⟩ := ih (fun k hk ↦ hT k (by omega))
      obtain ⟨f, _⟩ := exists_iso_binaryBiproduct_of_distTriang
        (Triangle.mk (0 : X n ⟶ X n) (ι n) (π n)).rotate
        (rot_of_distTriang _ (hT n (by omega))) (by
          change -(shiftFunctor C (1 : ℤ)).map (0 : X n ⟶ X n) = 0
          rw [Functor.map_zero, neg_zero])
      exact ⟨f ≪≫ biprod.mapIso e ((shiftFunctor C (1 : ℤ)).mapIso e)⟩

variable {A : Type*} [Category* A] [Abelian A]
  (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]

include hT in
/-- 最終項の零ホモロジーから、同じ次数の初項の零ホモロジーを得る。 -/
lemma iteratedZeroCone_isZero_first (q : ℤ) (h : IsZero ((F.shift q).obj (X n))) :
    IsZero ((F.shift q).obj (X 0)) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      have hs := homologySequence_shortExact_of_zero F _ (hT n (by omega)) rfl q
      have : Mono ((F.shift q).map (ι n)) := hs.mono_f
      exact ih (fun k hk ↦ hT k (by omega)) (IsZero.of_mono ((F.shift q).map (ι n)) h)

include hT in
/-- 最終項の零ホモロジーから、n 次進んだ初項の零ホモロジーを得る。 -/
lemma iteratedZeroCone_isZero_last (q : ℤ) (h : IsZero ((F.shift q).obj (X n))) :
    IsZero ((F.shift (q + n)).obj (X 0)) := by
  induction n generalizing q with
  | zero => simpa using h
  | succ n ih =>
      have hs := homologySequence_shortExact_of_zero F _ (hT n (by omega)) rfl q
      have := hs.epi_g
      have h' := ih (fun k hk ↦ hT k (by omega)) (q + 1) (IsZero.of_epi
        (F.homologySequenceδ (Triangle.mk (0 : X n ⟶ X n) (ι n) (π n)) q (q + 1) rfl) h)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using h'

include hT in
/-- n 回の零射の錐が [a,b] に集中すれば、初項は [a+n,b] に集中する。 -/
theorem iteratedZeroCone_vanishing (a b : ℤ)
    (h : ∀ q, q < a ∨ b < q → IsZero ((F.shift q).obj (X n)))
    (q : ℤ) (hq : q < a + n ∨ b < q) : IsZero ((F.shift q).obj (X 0)) := by
  rcases hq with hq | hq
  · have hz := iteratedZeroCone_isZero_last X ι π n hT F (q - n)
      (h _ (Or.inl (by omega)))
    simpa using hz
  · exact iteratedZeroCone_isZero_first X ι π n hT F q (h q (Or.inr hq))

include hT in
/-- homological 添字での新交叉型の消滅。m<n も含む。 -/
theorem iteratedZeroCone_homological_vanishing (m : ℤ)
    (h : ∀ i, i < 0 ∨ m < i → IsZero ((F.shift (-i)).obj (X n)))
    (i : ℤ) (hi : i < 0 ∨ m - n < i) : IsZero ((F.shift (-i)).obj (X 0)) := by
  apply iteratedZeroCone_vanishing X ι π n hT F (-m) 0
  · intro q hq
    simpa using h (-q) (by omega)
  · omega

include hT in
/-- 初項の正の cochain 次数の消滅は、零射の反復錐でも保たれる。 -/
lemma iteratedZeroCone_isZero_above (b : ℤ)
    (h : ∀ q, b < q → IsZero ((F.shift q).obj (X 0))) :
    ∀ q, b < q → IsZero ((F.shift q).obj (X n)) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro q hq
      have hz := ih (fun k hk ↦ hT k (by omega))
      have hs := homologySequence_shortExact_of_zero F _ (hT n (by omega)) rfl q
      exact hs.exact.isZero_X₂ ((hz q hq).eq_of_src _ _) ((hz (q + 1) (by omega)).eq_of_tgt _ _)

include hT in
/-- 負の homological 次数が消えれば、反復錐は第零ホモロジーを変えない。 -/
lemma iteratedZeroCone_homology_zero_iso
    (h : ∀ q : ℤ, 0 < q → IsZero ((F.shift q).obj (X 0))) :
    Nonempty ((F.shift (0 : ℤ)).obj (X 0) ≅ (F.shift (0 : ℤ)).obj (X n)) := by
  induction n with
  | zero => exact ⟨Iso.refl _⟩
  | succ n ih =>
      have ht : ∀ k < n, Triangle.mk (0 : X k ⟶ X k) (ι k) (π k) ∈ distTriang C :=
        fun k hk ↦ hT k (by omega)
      obtain ⟨e⟩ := ih ht
      have hs := homologySequence_shortExact_of_zero F _ (hT n (by omega)) rfl 0
      have : IsIso ((F.shift (0 : ℤ)).map (ι n)) := hs.isIso_f_iff.mpr
        (iteratedZeroCone_isZero_above X ι π n ht F 0 h 1 (by omega))
      exact ⟨e ≪≫ asIso ((F.shift (0 : ℤ)).map (ι n))⟩

include hT in
/-- 対象の分裂に対応する長さの二項係数公式。 -/
lemma iteratedZeroCone_length_binomial (l : A → ℝ)
    (ha : ∀ {S : ShortComplex A}, S.ShortExact → l S.X₂ = l S.X₁ + l S.X₃) (q : ℤ) :
    l ((F.shift q).obj (X n)) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * l ((F.shift (q + j)).obj (X 0)) :=
  coneLength_binomial_of_recurrence (fun k q ↦ l ((F.shift q).obj (X k))) n
    (fun k hk q ↦ homologyLength_zero_cone F l ha _ (hT k hk) rfl q) q

include hT in
/-- 反復錐の第零ホモロジーからの全射によって、初項の長さを下から評価する。 -/
lemma iteratedZeroCone_length_lower_bound (l : A → ℝ)
    (hi : ∀ {Y Z : A}, (Y ≅ Z) → l Y = l Z)
    (ha : ∀ {S : ShortComplex A}, S.ShortExact → l S.X₂ = l S.X₁ + l S.X₃)
    (hn : ∀ Y, 0 ≤ l Y)
    (h : ∀ q : ℤ, 0 < q → IsZero ((F.shift q).obj (X 0)))
    {Y : A} (f : (F.shift (0 : ℤ)).obj (X n) ⟶ Y) [Epi f] :
    l Y ≤ l ((F.shift (0 : ℤ)).obj (X 0)) := by
  obtain ⟨e⟩ := iteratedZeroCone_homology_zero_iso X ι π n hT F h
  rw [hi e]
  exact additiveLength_le_of_epi l ha hn f

include hT in
/-- 振幅が錐の個数に等しいとき、初項の Euler 評価は反復錐の第零次の長さに等しい。
消滅（`iteratedZeroCone_vanishing`）で初項のホモロジーが第零次に集中し、
第零次は反復錐で変わらない（`iteratedZeroCone_homology_zero_iso`）。 -/
theorem iteratedZeroCone_euler_eq_length_zero (l : A → ℝ)
    (hi : ∀ {Y Z : A}, (Y ≅ Z) → l Y = l Z) (hz : ∀ Y, IsZero Y → l Y = 0)
    (h : ∀ q : ℤ, q < -(n : ℤ) ∨ 0 < q → IsZero ((F.shift q).obj (X n))) :
    homologicalEuler l F (X 0) = l ((F.shift (0 : ℤ)).obj (X n)) := by
  have hv (q : ℤ) (hq : q ≠ 0) : IsZero ((F.shift q).obj (X 0)) :=
    iteratedZeroCone_vanishing X ι π n hT F (-(n : ℤ)) 0 h q (by omega)
  rw [homologicalEuler_eq_length_zero l F hz (X 0) hv]
  obtain ⟨e⟩ := iteratedZeroCone_homology_zero_iso X ι π n hT F (fun q hq ↦ hv q (by omega))
  exact hi e

include hT in
/-- 振幅が錐の個数に等しいとき、全射の下界は Euler 評価の下界になる。 -/
theorem iteratedZeroCone_euler_lower_bound (l : A → ℝ)
    (hi : ∀ {Y Z : A}, (Y ≅ Z) → l Y = l Z)
    (ha : ∀ {S : ShortComplex A}, S.ShortExact → l S.X₂ = l S.X₁ + l S.X₃)
    (hn : ∀ Y, 0 ≤ l Y) (hz : ∀ Y, IsZero Y → l Y = 0)
    (h : ∀ q : ℤ, q < -(n : ℤ) ∨ 0 < q → IsZero ((F.shift q).obj (X n)))
    {Y : A} (f : (F.shift (0 : ℤ)).obj (X n) ⟶ Y) [Epi f] :
    l Y ≤ homologicalEuler l F (X 0) := by
  rw [iteratedZeroCone_euler_eq_length_zero X ι π n hT F l hi hz h]
  exact additiveLength_le_of_epi l ha hn f

section Scalar

variable {R : Type*} [CommRing R] [Linear R C]
  [∀ q : ℤ, (shiftFunctor C q).Linear R]
  (x : ℕ → R)
  (hS : ∀ k < n, Triangle.mk (x k • 𝟙 (X k)) (ι k) (π k) ∈ distTriang C)
  (hx : ∀ j < n, x j • 𝟙 (X 0) = 0)

include hS hx in
/-- 初項で零な各スカラーは、他の零スカラーの錐を取った後も零である。 -/
lemma iteratedScalarCone_smul_zero (k : ℕ) (hk : k ≤ n) :
    ∀ j < n, x j • 𝟙 (X k) = 0 := by
  induction k with
  | zero => exact hx
  | succ k ih =>
      have hz := ih (by omega)
      intro j hj
      exact scalar_zero_on_zero_cone _ (hS k (by omega)) (hz k (by omega))
        (x j) (hz j hj) (hz j hj)

include hS hx in
/-- 初項を消す任意のスカラーは、零作用スカラーの錐を取った全段を消す。
このスカラー自身が錐を作る列に含まれることは要求しない。 -/
lemma iteratedScalarCone_smul_zero_of_smul_zero (a : R)
    (ha : a • 𝟙 (X 0) = 0) (k : ℕ) (hk : k ≤ n) : a • 𝟙 (X k) = 0 := by
  induction k with
  | zero => exact ha
  | succ k ih =>
    exact scalar_zero_on_zero_cone _ (hS k (by omega))
      (iteratedScalarCone_smul_zero X ι π n x hS hx k (by omega) k (by omega))
      a (ih (by omega)) (ih (by omega))

include hS hx in
/-- (Supp) を満たすスカラーの錐の列を、零射の錐の列として扱う。 -/
lemma iteratedScalarCone_zero_triangles :
    ∀ k < n, Triangle.mk (0 : X k ⟶ X k) (ι k) (π k) ∈ distTriang C := by
  intro k hk
  have hz := iteratedScalarCone_smul_zero X ι π n x hS hx k (by omega) k hk
  simpa only [hz] using hS k hk

include hS hx in
/-- スカラーの零作用と反復錐の振幅から得られる新交叉型の消滅。 -/
theorem iteratedScalarCone_homological_vanishing (m : ℤ)
    (h : ∀ i, i < 0 ∨ m < i → IsZero ((F.shift (-i)).obj (X n)))
    (i : ℤ) (hi : i < 0 ∨ m - n < i) : IsZero ((F.shift (-i)).obj (X 0)) :=
  iteratedZeroCone_homological_vanishing X ι π n
    (iteratedScalarCone_zero_triangles X ι π n x hS hx) F m h i hi

end Scalar

end SerrePositivity

end IteratedConePart

section ConeLengthCancellationPart

namespace SerrePositivity

/-- 一段の零射の錐の係数から、上に有界な元の係数列を復元できる。 -/
lemma coneLength_cancel (f g : ℤ → ℝ) (a : ℤ)
    (hf : ∀ q, a ≤ q → f q = 0) (hg : ∀ q, a ≤ q → g q = 0)
    (h : (cochainLengthShift + 1) f = (cochainLengthShift + 1) g) : f = g := by
  funext q
  by_cases hq : a ≤ q
  · rw [hf q hq, hg q hq]
  · apply Int.leInductionDown (motive := fun q _ ↦ f q = g q)
      ((hf a le_rfl).trans (hg a le_rfl).symm) ?_ q (by omega)
    intro k _ hk
    have he := congrFun h (k - 1)
    simp only [LinearMap.add_apply, cochainLengthShift_apply, Module.End.one_apply,
      Pi.add_apply, sub_add_cancel] at he
    linarith

/-- 反復錐の係数列も同じ上限より上では消える。 -/
lemma coneLength_pow_eq_zero_above (n : ℕ) (f : ℤ → ℝ) (a : ℤ)
    (hf : ∀ q, a ≤ q → f q = 0) (q : ℤ) (hq : a ≤ q) :
    ((cochainLengthShift + 1) ^ n) f q = 0 := by
  induction n generalizing q with
  | zero => simpa using hf q hq
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    simp only [LinearMap.add_apply, cochainLengthShift_apply, Module.End.one_apply,
      Pi.add_apply, ih q hq, ih (q + 1) (by omega), add_zero]

/-- 任意回数の反復錐の係数が一致すれば、上に有界な元の係数も一致する。 -/
lemma coneLength_pow_cancel (n : ℕ) (f g : ℤ → ℝ) (a : ℤ)
    (hf : ∀ q, a ≤ q → f q = 0) (hg : ∀ q, a ≤ q → g q = 0)
    (h : ((cochainLengthShift + 1) ^ n) f = ((cochainLengthShift + 1) ^ n) g) :
    f = g := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply] at h
    exact ih (coneLength_cancel _ _ a
      (coneLength_pow_eq_zero_above n f a hf)
      (coneLength_pow_eq_zero_above n g a hg) h)

/-- 二項係数公式を両側で確認すれば、各次数の評価が一意に決まる。 -/
theorem coneLength_binomial_cancel (n : ℕ) (f g : ℤ → ℝ) (a : ℤ)
    (hf : ∀ q, a ≤ q → f q = 0) (hg : ∀ q, a ≤ q → g q = 0)
    (h : ∀ q, (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * f (q + j)) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * g (q + j)) : f = g := by
  apply coneLength_pow_cancel n f g a hf hg
  funext q
  simpa only [coneLength_binomial] using h q

/-- 有限支持の評価と上に有界な極限列は、二項変換の一致から同定できる。 -/
theorem coneLength_binomial_cancel_of_hasFiniteSupport (n : ℕ) (f g : ℤ → ℝ)
    (hf : Function.HasFiniteSupport f) (a : ℤ) (hg : ∀ q, a ≤ q → g q = 0)
    (h : ∀ q, (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * f (q + j)) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * g (q + j)) : f = g := by
  obtain ⟨b, hb⟩ := hf.bddAbove
  apply coneLength_binomial_cancel n f g (max a (b + 1)) ?_ ?_ h
  · intro q hq
    by_contra hn
    have := hb (show q ∈ Function.support f from hn)
    omega
  · intro q hq
    exact hg q (le_trans (le_max_left _ _) hq)

/-- 有限支持の二つの係数列について、同じ回数の零錐を消去できる。 -/
theorem coneLength_pow_cancel_of_hasFiniteSupport (n : ℕ) (f g : ℤ → ℝ)
    (hf : Function.HasFiniteSupport f) (hg : Function.HasFiniteSupport g)
    (h : ((cochainLengthShift + 1) ^ n) f = ((cochainLengthShift + 1) ^ n) g) : f = g := by
  obtain ⟨b, hb⟩ := hg.bddAbove
  apply coneLength_binomial_cancel_of_hasFiniteSupport n f g hf (b + 1) ?_ ?_
  · intro q hq
    by_contra hn
    have := hb (show q ∈ Function.support g from hn)
    omega
  · intro q
    simpa only [coneLength_binomial] using congrFun h q

end SerrePositivity

end ConeLengthCancellationPart
