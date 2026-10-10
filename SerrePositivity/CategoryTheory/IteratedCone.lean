module

public import SerrePositivity.CategoryTheory.ScalarZeroCone
public import SerrePositivity.CategoryTheory.HomologicalConeLength
public import SerrePositivity.CategoryTheory.AdditiveLength
public import SerrePositivity.CategoryTheory.ConeLengthBinomial

/-! # 反復錐の分裂と新交叉型の消滅

反復錐は対象列と各段の完全三角形で与える。テンソル積や関手的な錐は使わない。
内部では cochain 添字を使い、最後に homological 添字へ変換する。
消滅は零対象について証明し、長さやその忠実性を仮定しない。
-/

@[expose] public section

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
/-- 振幅が錐の個数に等しいとき、全射の下界は Euler 評価の下界になる。 -/
theorem iteratedZeroCone_euler_lower_bound (l : A → ℝ)
    (hi : ∀ {Y Z : A}, (Y ≅ Z) → l Y = l Z)
    (ha : ∀ {S : ShortComplex A}, S.ShortExact → l S.X₂ = l S.X₁ + l S.X₃)
    (hn : ∀ Y, 0 ≤ l Y) (hz : ∀ Y, IsZero Y → l Y = 0)
    (h : ∀ q : ℤ, q < -(n : ℤ) ∨ 0 < q → IsZero ((F.shift q).obj (X n)))
    {Y : A} (f : (F.shift (0 : ℤ)).obj (X n) ⟶ Y) [Epi f] :
    l Y ≤ homologicalEuler l F (X 0) := by
  have hv (q : ℤ) (hq : q ≠ 0) : IsZero ((F.shift q).obj (X 0)) :=
    iteratedZeroCone_vanishing X ι π n hT F (-(n : ℤ)) 0 h q (by omega)
  rw [homologicalEuler_eq_length_zero l F hz (X 0) hv]
  exact iteratedZeroCone_length_lower_bound X ι π n hT F l hi ha hn
    (fun q hq ↦ hv q (by omega)) f

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
