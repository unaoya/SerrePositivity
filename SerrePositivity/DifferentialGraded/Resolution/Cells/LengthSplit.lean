module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.LengthGraded
public import SerrePositivity.DifferentialGraded.Tensor.ObjectwiseKFlat

/-! # path長filtrationの次数ごとの分裂と有限段階のK-flat性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

omit [Small.{u} I] in
lemma lengthSet_subset_succ (n : ℕ) : lengthSet I n ⊆ lengthSet I (n + 1) :=
  fun _ h => Nat.le_trans h (Nat.le_succ n)

omit [Small.{u} I] in
lemma exactLengthSet_subset (n : ℕ) : exactLengthSet I n ⊆ lengthSet I n :=
  fun _ h => Nat.le_of_eq h

omit [Small.{u} I] in
lemma lengthSet_disjoint_exact_succ (n : ℕ) : Disjoint (lengthSet I n) (exactLengthSet I (n + 1)) :=
  Set.disjoint_left.mpr (by
    intro w hw ht
    change w.length ≤ n at hw
    change w.length = n + 1 at ht
    omega)

omit [Small.{u} I] in
lemma lengthSet_partition_succ (n : ℕ) :
    lengthSet I (n + 1) ⊆ lengthSet I n ∪ exactLengthSet I (n + 1) := by
  intro w hw
  change w.length ≤ n + 1 at hw
  change w.length ≤ n ∨ w.length = n + 1
  omega

lemma lengthMap_quotient (n : ℕ) (x y : D) :
    C.lengthMap A D I n (n + 1) (Nat.le_succ n) x y ≫
      C.lengthQuotient A D I (n + 1) x y = 0 := by
  have h := ComplexCoproduct.select_comp (fun w => C.term A D I w x y)
    (lengthSet I n) (lengthSet I (n + 1)) (exactLengthSet I (n + 1)) (lengthSet_subset_succ I n)
  rw [ComplexCoproduct.select_zero _ _ _ (lengthSet_disjoint_exact_succ I n)] at h
  apply HomologicalComplex.Hom.ext
  funext i
  change ((ComplexCoproduct.select (fun w => C.term A D I w x y)
    (lengthSet I n) (lengthSet I (n + 1))).f i) ≫
    ((ComplexCoproduct.select (fun w => C.term A D I w x y)
      (lengthSet I (n + 1)) (exactLengthSet I (n + 1))).f i) = 0
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
    congrArg (fun f => f.f i) h

def lengthShortComplex (n : ℕ) (x y : D) : ShortComplex (Complex A) :=
  ShortComplex.mk (C.lengthMap A D I n (n + 1) (Nat.le_succ n) x y)
    (C.lengthQuotient A D I (n + 1) x y) (C.lengthMap_quotient A D I n x y)

def lengthSplitting (n : ℕ) (x y : D) (i : ℤ) :
    ((C.lengthShortComplex A D I n x y).map
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)).Splitting where
  r := (ComplexCoproduct.select (fun w => C.term A D I w x y)
    (lengthSet I (n + 1)) (lengthSet I n)).f i
  s := (ComplexCoproduct.select (fun w => C.term A D I w x y)
    (exactLengthSet I (n + 1)) (lengthSet I (n + 1))).f i
  f_r := by
    change (ComplexCoproduct.select (fun w => C.term A D I w x y)
      (lengthSet I n) (lengthSet I (n + 1))).f i ≫
      (ComplexCoproduct.select (fun w => C.term A D I w x y)
        (lengthSet I (n + 1)) (lengthSet I n)).f i = 𝟙 _
    have h := ComplexCoproduct.select_comp (fun w => C.term A D I w x y)
      (lengthSet I n) (lengthSet I (n + 1)) (lengthSet I n) (lengthSet_subset_succ I n)
    rw [ComplexCoproduct.select_self] at h
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f => f.f i) h
  s_g := by
    change (ComplexCoproduct.select (fun w => C.term A D I w x y)
      (exactLengthSet I (n + 1)) (lengthSet I (n + 1))).f i ≫
      (ComplexCoproduct.select (fun w => C.term A D I w x y)
        (lengthSet I (n + 1)) (exactLengthSet I (n + 1))).f i = 𝟙 _
    have h := ComplexCoproduct.select_comp (fun w => C.term A D I w x y)
      (exactLengthSet I (n + 1)) (lengthSet I (n + 1)) (exactLengthSet I (n + 1))
      (exactLengthSet_subset I (n + 1))
    rw [ComplexCoproduct.select_self] at h
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f => f.f i) h
  id := by
    change
      (ComplexCoproduct.select (fun w => C.term A D I w x y)
        (lengthSet I (n + 1)) (lengthSet I n)).f i ≫
        (ComplexCoproduct.select (fun w => C.term A D I w x y)
          (lengthSet I n) (lengthSet I (n + 1))).f i +
      (ComplexCoproduct.select (fun w => C.term A D I w x y)
        (lengthSet I (n + 1)) (exactLengthSet I (n + 1))).f i ≫
        (ComplexCoproduct.select (fun w => C.term A D I w x y)
          (exactLengthSet I (n + 1)) (lengthSet I (n + 1))).f i = 𝟙 _
    have h := ComplexCoproduct.select_partition (fun w => C.term A D I w x y)
      (lengthSet I n) (exactLengthSet I (n + 1)) (lengthSet I (n + 1))
      (lengthSet_subset_succ I n) (exactLengthSet_subset I (n + 1))
      (lengthSet_disjoint_exact_succ I n) (lengthSet_partition_succ I n)
    simpa only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      HomologicalComplex.id_f] using congrArg (fun f => f.f i) h

instance lengthQuotient_zero_isIso (x y : D) : IsIso (C.lengthQuotient A D I 0 x y) := by
  have h0 : lengthSet I 0 = exactLengthSet I 0 := by
    ext w
    change w.length ≤ 0 ↔ w.length = 0
    omega
  have hs : IsIso (C.lengthInternalQuotient A D I 0 x y) := by
    change IsIso (ComplexCoproduct.select (fun w => C.term A D I w x y)
      (lengthSet I 0) (exactLengthSet I 0))
    rw [← h0, ComplexCoproduct.select_self]
    infer_instance
  have : ∀ i, IsIso ((C.lengthQuotient A D I 0 x y).f i) := by
    intro i
    change IsIso ((C.lengthInternalQuotient A D I 0 x y).f i)
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

lemma lengthHom_kFlat (hD : localHomKFlat A D) (n : ℕ) (x y : D) :
    complexKFlat A (C.lengthHom A D I n x y) := by
  induction n with
  | zero =>
    exact complexKFlat_of_iso A (asIso (C.lengthQuotient A D I 0 x y))
      (C.exactLengthHom_kFlat A D I hD 0 x y)
  | succ n ih =>
    exact complexKFlat_of_degreewiseSplit A (C.lengthShortComplex A D I n x y)
      (C.lengthSplitting A D I n x y) ih (C.exactLengthHom_kFlat A D I hD (n + 1) x y)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
