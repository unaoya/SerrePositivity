module

public import SerrePositivity.DifferentialGraded.Quotient.Path.Construction
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainInterchange
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import SerrePositivity.DifferentialGraded.Complexes.TensorClosedZero
public import SerrePositivity.DifferentialGraded.Complexes.UnitorCochainNaturality
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainNaturality
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainFactors

/-!
# Quotient.Erasure

## 概要
15 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## ErasureFaces（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureFaces.lean） -/

/-! # 有限pathの各収縮記号を消すcochain

εを消した後、隣接する元のHomを豊穣合成する。後方のεへは全次数tensor写像で進むので、
先行するHomの次数とεの次数−1に由来するKoszul符号が保たれる。
ここでは内部微分に関する閉性を証明し、消去項の和の二乗零は後続で扱う。
-/

@[expose] public section ErasureFaces
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 先頭のεを消し、隣り合うHomを合成する次数+1のcochain。 -/
def eraseFirst {S : Set D} (b : S) (w : Word S) (x y : D) :
    Cochain (term A D (b :: w) x y) (term A D w x y) 1 :=
  (eraseMiddle A (homObject A D x b.val) (term A D w b.val y)).comp
    (Cochain.ofHom (prependMap A D w x b.val y)) (add_zero 1)

lemma eraseFirst_closed {S : Set D} (b : S) (w : Word S) (x y : D) :
    δ 1 2 (eraseFirst A D b w x y) = 0 := by
  rw [eraseFirst, δ_comp_ofHom, eraseMiddle_closed]
  exact Cochain.zero_comp _ _

/-- i番目のεを消す。範囲外の添字は零とする。 -/
def eraseFace {S : Set D} : ∀ (w : Word S) (i : ℕ) (x y : D),
    Cochain (term A D w x y) (term A D (w.eraseIdx i) x y) 1
  | [], _, _, _ => 0
  | b :: w, 0, x, y => eraseFirst A D b w x y
  | b :: w, i + 1, x, y =>
    (tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y)
      (epsilonComplex A ⊗ term A D (w.eraseIdx i) b.val y)).f 1
      ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
        (term A D (w.eraseIdx i) b.val y)).f 1 (eraseFace w i b.val y))

@[simp] lemma eraseFace_nil (S : Set D) (i : ℕ) (x y : D) :
    eraseFace A D ([] : Word S) i x y = 0 := rfl

@[simp] lemma eraseFace_zero {S : Set D} (b : S) (w : Word S) (x y : D) :
    eraseFace A D (b :: w) 0 x y = eraseFirst A D b w x y := rfl

/-- 各ε消去は内部微分と反交換する。 -/
lemma eraseFace_closed {S : Set D} (w : Word S) (i : ℕ) (x y : D) :
    δ 1 2 (eraseFace A D w i x y) = 0 := by
  induction w generalizing i x y with
  | nil => simp only [eraseFace, δ_zero]
  | cons b w ih =>
    cases i with
    | zero => exact eraseFirst_closed A D b w x y
    | succ i =>
      exact homComplexMap_closed _ 1 _ (homComplexMap_closed _ 1 _ (ih i b.val y))

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureFaces

/-! ## ErasureRows（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureRows.lean） -/

/-! # 各有限pathから全path直和へのε消去項

長さrのpathについてr個の消去cochainを足す。各項の終域を対応する短いpathの包含で揃える。
全直和の自己cochainとその二乗零は後続で構成する。
-/

@[expose] public section ErasureRows
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- i番目の消去を、消去後のpathの全直和への包含と合成する。 -/
def eraseSummand {S : Set D} (w : Word S) (i : ℕ) (x y : D) :
    Cochain (term A D w x y) (internalHom A D S x y) 1 :=
  (eraseFace A D w i x y).comp
    (Cochain.ofHom (ι A D S x y (w.eraseIdx i))) (add_zero 1)

lemma eraseSummand_closed {S : Set D} (w : Word S) (i : ℕ) (x y : D) :
    δ 1 2 (eraseSummand A D w i x y) = 0 := by
  rw [eraseSummand, δ_comp_ofHom, eraseFace_closed]
  exact Cochain.zero_comp _ _

/-- 一つのpath上のε消去微分。和はその有限長にわたる。 -/
def eraseRow {S : Set D} (w : Word S) (x y : D) :
    Cochain (term A D w x y) (internalHom A D S x y) 1 :=
  ∑ i ∈ Finset.range w.length, eraseSummand A D w i x y

/-- 有限消去和も内部微分と反交換する。 -/
lemma eraseRow_closed {S : Set D} (w : Word S) (x y : D) :
    δ 1 2 (eraseRow A D w x y) = 0 := by
  change (δ_hom ℤ _ _ 1 2) (eraseRow A D w x y) = 0
  simp only [eraseRow, map_sum, δ_hom_apply, eraseSummand_closed,
    Finset.sum_const_zero]

@[simp] lemma eraseRow_nil (S : Set D) (x y : D) :
    eraseRow A D ([] : Word S) x y = 0 := by simp [eraseRow]

lemma eraseRow_singleton {S : Set D} (b : S) (x y : D) :
    eraseRow A D [b] x y = (eraseFirst A D b [] x y).comp
      (Cochain.ofHom (originalHom A D S x y)) (add_zero 1) := by
  simp only [eraseRow, List.length_cons, List.length_nil, zero_add, Finset.range_one,
    Finset.sum_singleton]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureRows

/-! ## ErasureOperator（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureOperator.lean） -/

/-! # 全path直和上のε消去作用素

閉じた次数+1の各消去和をshift先へのchain mapへ移し、直和の普遍性で貼り合わせる。
得られる作用素は内部微分と反交換する。作用素自身の二乗零は別に証明する必要がある。
-/

@[expose] public section ErasureOperator
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 各pathの閉じた消去和を次数+1のcocycleとして保持する。 -/
def eraseRowCycle {S : Set D} (w : Word S) (x y : D) :
    Cocycle (term A D w x y) (internalHom A D S x y) 1 :=
  Cocycle.mk (eraseRow A D w x y) 2 (by omega) (eraseRow_closed A D w x y)

/-- 直和普遍性によるshift先への消去chain map。 -/
def erasureToShift (S : Set D) (x y : D) :
    internalHom A D S x y ⟶ (internalHom A D S x y)⟦(1 : ℤ)⟧ :=
  Sigma.desc (fun w => Cocycle.equivHomShift.symm (eraseRowCycle A D w x y))

lemma ι_erasureToShift (S : Set D) (x y : D) (w : Word S) :
    ι A D S x y w ≫ erasureToShift A D S x y =
      Cocycle.equivHomShift.symm (eraseRowCycle A D w x y) :=
  Sigma.ι_comp_desc _ _

/-- 全path直和上の次数+1のε消去cocycle。 -/
def erasureCycle (S : Set D) (x y : D) :
    Cocycle (internalHom A D S x y) (internalHom A D S x y) 1 :=
  Cocycle.equivHomShift (erasureToShift A D S x y)

/-- 内部微分に加える、path長を一つ下げる次数+1の作用素。 -/
def erasure (S : Set D) (x y : D) :
    Cochain (internalHom A D S x y) (internalHom A D S x y) 1 :=
  (erasureCycle A D S x y).val

lemma erasure_closed (S : Set D) (x y : D) : δ 1 2 (erasure A D S x y) = 0 :=
  Cocycle.δ_eq_zero _ _

/-- 作用素を各pathへ制限すると、元の有限消去和になる。 -/
lemma erasure_precomp (S : Set D) (x y : D) (w : Word S) :
    (Cochain.ofHom (ι A D S x y w)).comp (erasure A D S x y) (zero_add 1) =
      eraseRow A D w x y := by
  have h := congrArg (fun f => (Cocycle.equivHomShift f).val)
    (ι_erasureToShift A D S x y w)
  rw [Cocycle.equivHomShift_comp, AddEquiv.apply_symm_apply] at h
  exact h

/-- 元のHomに対応する空path上ではε消去は零。 -/
lemma erasure_originalHom (S : Set D) (x y : D) :
    (Cochain.ofHom (originalHom A D S x y)).comp (erasure A D S x y) (zero_add 1) = 0 := by
  exact (erasure_precomp A D S x y []).trans (eraseRow_nil A D S x y)

/-- 各path上で二重消去は、最初のfaceと短いpathの消去和の合成の有限和になる。 -/
lemma erasure_square_precomp (S : Set D) (x y : D) (w : Word S) :
    (Cochain.ofHom (ι A D S x y w)).comp
      ((erasure A D S x y).comp (erasure A D S x y) (show (1 : ℤ) + 1 = 2 by omega))
      (zero_add 2) =
    ∑ i ∈ Finset.range w.length, (eraseFace A D w i x y).comp
      (eraseRow A D (w.eraseIdx i) x y) (show (1 : ℤ) + 1 = 2 by omega) := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, erasure_precomp]
  let R : Cochain (term A D w x y) (internalHom A D S x y) 1 →+
      Cochain (term A D w x y) (internalHom A D S x y) 2 :=
    { toFun := fun f => f.comp (erasure A D S x y) (by omega)
      map_zero' := Cochain.zero_comp _ _
      map_add' := fun f g => Cochain.add_comp f g _ _ }
  change R (eraseRow A D w x y) = _
  rw [eraseRow, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (eraseSummand A D w i x y).comp (erasure A D S x y) (by omega) = _
  rw [eraseSummand, Cochain.comp_assoc_of_second_is_zero_cochain, erasure_precomp]

/-- 空pathでは二重消去も零。 -/
lemma erasure_square_originalHom (S : Set D) (x y : D) :
    (Cochain.ofHom (originalHom A D S x y)).comp
      ((erasure A D S x y).comp (erasure A D S x y) (show (1 : ℤ) + 1 = 2 by omega))
      (zero_add 2) = 0 := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, erasure_originalHom]
  exact Cochain.zero_comp _ _

/-- 長さ1のpathは一度消去すると空pathとなるため、二重消去は零。 -/
lemma erasure_square_singleton {S : Set D} (b : S) (x y : D) :
    (Cochain.ofHom (ι A D S x y [b])).comp
      ((erasure A D S x y).comp (erasure A D S x y) (show (1 : ℤ) + 1 = 2 by omega))
      (zero_add 2) = 0 := by
  rw [erasure_square_precomp]
  simp only [List.length_cons, List.length_nil, zero_add, Finset.range_one,
    Finset.sum_singleton]
  change (eraseFirst A D b [] x y).comp (eraseRow A D ([] : Word S) x y) (by omega) = 0
  rw [eraseRow_nil]
  exact Cochain.comp_zero _ _

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureOperator

/-! ## ErasureInterchange（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureInterchange.lean） -/

/-! # ε消去と後方cochainの反交換

単位因子を除く前のε消去について、右隣の次数+1 cochainと順序交換すると負号が付く。
任意の非有界複体を前に置いても、この反交換式は全次数tensor写像で保存される。
-/

@[expose] public section ErasureInterchange
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- ε消去と右隣の次数+1 cochainの反交換。 -/
lemma eraseRightTensor_tail_anticommute (P Q : Complex A) (f : Cochain P Q 1) :
    (eraseRightTensor A P).comp ((tensorLeftHom (𝟙_ (Complex A)) P Q).f 1 f)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -(((tensorLeftHom (epsilonComplex A) P Q).f 1 f).comp (eraseRightTensor A Q)
      (show (1 : ℤ) + 1 = 2 by omega)) :=
  tensorCochain_odd_anticommute (epsilonComplex A) (𝟙_ (Complex A)) P Q (eraseEpsilon A) f

/-- 任意の前方因子でtensorした後も、ε消去と後方cochainは反交換する。 -/
lemma eraseRightTensor_prefixed_anticommute (K P Q : Complex A) (f : Cochain P Q 1) :
    ((tensorLeftHom K (epsilonComplex A ⊗ P) (𝟙_ (Complex A) ⊗ P)).f 1
      (eraseRightTensor A P)).comp
      ((tensorLeftHom K (𝟙_ (Complex A) ⊗ P) (𝟙_ (Complex A) ⊗ Q)).f 1
        ((tensorLeftHom (𝟙_ (Complex A)) P Q).f 1 f))
      (show (1 : ℤ) + 1 = 2 by omega) =
    -(((tensorLeftHom K (epsilonComplex A ⊗ P) (epsilonComplex A ⊗ Q)).f 1
      ((tensorLeftHom (epsilonComplex A) P Q).f 1 f)).comp
      ((tensorLeftHom K (epsilonComplex A ⊗ Q) (𝟙_ (Complex A) ⊗ Q)).f 1
        (eraseRightTensor A Q)) (show (1 : ℤ) + 1 = 2 by omega)) :=
  tensorLeftHom_cochain_anticommute K _ _ _ _ 1 1 2 (by omega) (by omega)
    _ _ _ _ (eraseRightTensor_tail_anticommute A P Q f)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureInterchange

/-! ## ErasureCancellation（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureCancellation.lean） -/

/-! # 二つのεを消す順序の交換と有限和の相殺

最初の消去位置iと、消去後の位置jを、反対の順序の二つの位置へ移す。
固定点のない対合で相殺するため、標数2でも加法群の追加仮定を必要としない。
実際のpath cochainへの適用には、対応する二つの項が互いに負になることの証明が必要。
-/

@[expose] public section ErasureCancellation

namespace SerrePositivity.DifferentialGraded.DGQuotient

/-- 二回の消去順序を交換する。第二添字は最初の消去後の語で数える。 -/
def swapErasure (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.2 < p.1 then (p.2, p.1 - 1) else (p.2 + 1, p.1)

lemma swapErasure_involutive (p : ℕ × ℕ) : swapErasure (swapErasure p) = p := by
  rcases p with ⟨i, j⟩
  by_cases h : j < i
  · have hs : swapErasure (i, j) = (j, i - 1) := ite_eq_left h
    have hs' : swapErasure (j, i - 1) = (i - 1 + 1, j) :=
      ite_eq_right (by omega)
    rw [hs, hs']
    exact Prod.ext (by omega) rfl
  · have hs : swapErasure (i, j) = (j + 1, i) := ite_eq_right h
    have hs' : swapErasure (j + 1, i) = (i, j + 1 - 1) := ite_eq_left (by omega)
    rw [hs, hs']
    exact Prod.ext rfl (by omega)

lemma swapErasure_ne (p : ℕ × ℕ) : swapErasure p ≠ p := by
  rcases p with ⟨i, j⟩
  unfold swapErasure
  split_ifs <;> simp_all only [ne_eq, Prod.mk.injEq] <;> omega

lemma swapErasure_mem {n : ℕ} {p : ℕ × ℕ}
    (h : p ∈ (Finset.range n).product (Finset.range (n - 1))) :
    swapErasure p ∈ (Finset.range n).product (Finset.range (n - 1)) := by
  rcases p with ⟨i, j⟩
  have hi : i < n := Finset.mem_range.mp (Finset.mem_product.mp h).1
  have hj : j < n - 1 := Finset.mem_range.mp (Finset.mem_product.mp h).2
  by_cases hij : j < i
  · have hs : swapErasure (i, j) = (j, i - 1) := ite_eq_left hij
    rw [hs]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩
  · have hs : swapErasure (i, j) = (j + 1, i) := ite_eq_right hij
    rw [hs]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩

/-- 二重消去の項が順序交換で負になるなら、有限二重和は零。 -/
lemma erasure_double_sum_cancel {G : Type*} [AddCommGroup G] (n : ℕ) (f : ℕ → ℕ → G)
    (h : ∀ i < n, ∀ j < n - 1,
      f i j = -f (swapErasure (i, j)).1 (swapErasure (i, j)).2) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - 1), f i j = 0 := by
  rw [← Finset.sum_product' (Finset.range n) (Finset.range (n - 1)) f]
  apply Finset.sum_involution (fun p _ => swapErasure p)
  · intro p hp
    have hp' := hp
    simp only [Finset.mem_product, Finset.mem_range] at hp'
    exact eq_neg_iff_add_eq_zero.mp (h p.1 hp'.1 p.2 hp'.2)
  · intro p _ _
    exact swapErasure_ne p
  · intro p hp
    exact swapErasure_mem hp
  · intro p _
    exact swapErasure_involutive p

end SerrePositivity.DifferentialGraded.DGQuotient

end ErasureCancellation

/-! ## ErasureFaceEquations（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureFaceEquations.lean） -/

/-! # 先頭εを保つfaceの一段の再帰式

後方の再帰呼出しを展開せずに、先頭のtensor作用だけを公開する。
-/

@[expose] public section ErasureFaceEquations
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma eraseFace_cons_succ {S : Set D} (b : S) (w : Word S) (i : ℕ) (x y : D) :
    eraseFace A D (b :: w) (i + 1) x y =
    (tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y)
      (epsilonComplex A ⊗ term A D (w.eraseIdx i) b.val y)).f 1
      ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
        (term A D (w.eraseIdx i) b.val y)).f 1 (eraseFace A D w i b.val y)) := rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureFaceEquations

/-! ## ErasureRowRecursion（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureRowRecursion.lean） -/

/-! # 非空pathのε消去和を先頭と後方へ分ける再帰式 -/

@[expose] public section ErasureRowRecursion
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 後方cochainを先頭Homとεでtensorし、先頭を追加したpath直和へ送る。 -/
def prefixTailCochain {S : Set D} (b : S) (w : Word S) (x y : D) (p : ℤ)
    (f : Cochain (term A D w b.val y) (internalHom A D S b.val y) p) :
    Cochain (term A D (b :: w) x y) (internalHom A D S x y) p :=
  ((tensorLeftHom (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
    (epsilonComplex A ⊗ internalHom A D S b.val y)).f p
    ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
      (internalHom A D S b.val y)).f p f)).comp
    (Cochain.ofHom (prefixPath A D b x y)) (add_zero p)

/-- 後方の消去項は短いpathの消去項を二重tensorし、先頭を追加したもの。 -/
lemma eraseSummand_cons_succ {S : Set D} (b : S) (w : Word S) (i : ℕ) (x y : D) :
    eraseSummand A D (b :: w) (i + 1) x y =
    prefixTailCochain A D b w x y 1 (eraseSummand A D w i b.val y) := by
  rw [prefixTailCochain, eraseSummand, eraseSummand, eraseFace_cons_succ,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, prefixPath_ι]
  rfl

/-- 非空pathの消去和は、先頭εの消去と、先頭を保持する後方消去和の和である。 -/
lemma eraseRow_cons {S : Set D} (b : S) (w : Word S) (x y : D) :
    eraseRow A D (b :: w) x y =
    (eraseFirst A D b w x y).comp (Cochain.ofHom (ι A D S x y w)) (add_zero 1) +
    prefixTailCochain A D b w x y 1 (eraseRow A D w b.val y) := by
  let R : Cochain (term A D w b.val y) (internalHom A D S b.val y) 1 →+
      Cochain (term A D (b :: w) x y) (internalHom A D S x y) 1 :=
    { toFun := prefixTailCochain A D b w x y 1
      map_zero' := by simp only [prefixTailCochain, map_zero, Cochain.zero_comp]
      map_add' := fun f g => by
        simp only [prefixTailCochain, map_add]
        exact Cochain.add_comp _ _ _ (add_zero 1) }
  have hs : ∑ i ∈ Finset.range w.length, eraseSummand A D (b :: w) (i + 1) x y =
      R (eraseRow A D w b.val y) := by
    rw [eraseRow, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact eraseSummand_cons_succ A D b w i x y
  have hz : eraseSummand A D (b :: w) 0 x y =
      (eraseFirst A D b w x y).comp (Cochain.ofHom (ι A D S x y w)) (add_zero 1) := rfl
  rw [eraseRow, List.length_cons, Finset.sum_range_succ', hs, hz]
  exact add_comm _ _

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureRowRecursion

/-! ## ErasureTailComposition（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureTailComposition.lean） -/

/-! # 先頭記号を保つ二重消去の帰納式

二つの消去位置がともに先頭より後なら、二重消去は短いpathの二重消去を
先頭Homとεで二重に左tensorしたものになる。
-/

@[expose] public section ErasureTailComposition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 範囲外の位置でεを消すfaceは零である。 -/
lemma eraseFace_eq_zero_of_length_le {S : Set D} (w : Word S) (i : ℕ)
    (hi : w.length ≤ i) (x y : D) : eraseFace A D w i x y = 0 := by
  induction w generalizing i x y with
  | nil => rfl
  | cons b w ih =>
    cases i with
    | zero => simp only [List.length_cons] at hi; omega
    | succ i =>
      dsimp only [eraseFace]
      rw [ih i (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using hi),
        map_zero, map_zero]

/-- 二つとも先頭より後の消去なら、合成は短いpathでの合成から得られる。 -/
lemma eraseFace_succ_comp {S : Set D} (b : S) (w : Word S) (i j : ℕ) (x y : D) :
    (eraseFace A D (b :: w) (i + 1) x y).comp
      (eraseFace A D ((b :: w).eraseIdx (i + 1)) (j + 1) x y)
      (show (1 : ℤ) + 1 = 2 by omega) =
    (tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y)
      (epsilonComplex A ⊗ term A D ((w.eraseIdx i).eraseIdx j) b.val y)).f 2
      ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
        (term A D ((w.eraseIdx i).eraseIdx j) b.val y)).f 2
          ((eraseFace A D w i b.val y).comp
            (eraseFace A D (w.eraseIdx i) j b.val y) (by omega))) := by
  change
    (((tensorLeftHom (homObject A D x b.val) _ _).f 1
      ((tensorLeftHom (epsilonComplex A) _ _).f 1 (eraseFace A D w i b.val y))).comp
      ((tensorLeftHom (homObject A D x b.val) _ _).f 1
        ((tensorLeftHom (epsilonComplex A) _ _).f 1
          (eraseFace A D (w.eraseIdx i) j b.val y))) (by omega)) = _
  rw [← tensorLeftHom_cochain_comp, ← tensorLeftHom_cochain_comp]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureTailComposition

/-! ## ErasureMiddleInterchange（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureMiddleInterchange.lean） -/

/-! # 単位因子を除いた中間ε消去と後方cochainの反交換 -/

@[expose] public section ErasureMiddleInterchange
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 中間εを消した後に後方cochainを作用させる順序を交換すると負号が付く。 -/
lemma eraseMiddle_tail_anticommute (K P Q : Complex A) (f : Cochain P Q 1) :
    (eraseMiddle A K P).comp ((tensorLeftHom K P Q).f 1 f)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -(((tensorLeftHom K (epsilonComplex A ⊗ P) (epsilonComplex A ⊗ Q)).f 1
      ((tensorLeftHom (epsilonComplex A) P Q).f 1 f)).comp
      (eraseMiddle A K Q) (show (1 : ℤ) + 1 = 2 by omega)) := by
  rw [eraseMiddle, eraseMiddle, Cochain.comp_assoc_of_second_is_zero_cochain,
    ← leftUnitor_hom_cochain_tensor,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    eraseRightTensor_prefixed_anticommute, Cochain.neg_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain]

/-- 標準ε生成元を含む純tensorの消去は、左因子の次数の符号を持つ。 -/
lemma eraseMiddle_generator (K Q : Complex A) (i j b a n : ℤ)
    (hb : (-1) + j = b) (ha : i + b = a) (hn : a + 1 = n)
    (x : K.X i) (y : Q.X j) :
    (eraseMiddle A K Q).v a n hn
      (ιTensorObj K (epsilonComplex A ⊗ Q) i b a ha
        (x ⊗ₜ[A] ιTensorObj (epsilonComplex A) Q (-1) j b hb
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] y))) =
    i.negOnePow • ιTensorObj K Q i j n (by omega) (x ⊗ₜ[A] y) := by
  rw [eraseMiddle, cochain_comp_ofHom_apply,
    tensorLeftHom_apply_of_sum K (epsilonComplex A ⊗ Q) (𝟙_ (Complex A) ⊗ Q)
      1 i b a j n ha (by omega) hn,
    eraseRightTensor_apply, eraseEpsilon_generator, chain_units_smul,
    whiskerLeft_apply, leftUnitor_hom_generator]
  simp only [one_mul]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureMiddleInterchange

/-! ## ErasureHead（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureHead.lean） -/

/-! # 左端εの消去と中間消去のtensor表示 -/

@[expose] public section ErasureHead
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 左端のεを消し、単位因子も除く次数+1のcochain。 -/
def eraseHead (P : Complex A) : Cochain (epsilonComplex A ⊗ P) P 1 :=
  (eraseRightTensor A P).comp (Cochain.ofHom (λ_ P).hom) (add_zero 1)

lemma eraseHead_closed (P : Complex A) : δ 1 2 (eraseHead A P) = 0 := by
  rw [eraseHead, δ_comp_ofHom, eraseRightTensor_closed]
  exact Cochain.zero_comp _ _

/-- 中間ε消去は左端ε消去を左tensorしたものに等しい。 -/
lemma eraseMiddle_eq_tensorLeft (K P : Complex A) :
    eraseMiddle A K P = (tensorLeftHom K (epsilonComplex A ⊗ P) P).f 1 (eraseHead A P) := by
  rw [eraseHead, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom]
  rfl

/-- 前方二因子のchain mapによる合成は、その後のε消去と可換する。 -/
lemma tensorJoin_eraseMiddle (U V W P : Complex A) (c : U ⊗ V ⟶ W) :
    (Cochain.ofHom ((α_ U V (epsilonComplex A ⊗ P)).inv ≫ c ▷ (epsilonComplex A ⊗ P))).comp
      (eraseMiddle A W P) (zero_add 1) =
    ((tensorLeftHom U (V ⊗ (epsilonComplex A ⊗ P)) (V ⊗ P)).f 1
      (eraseMiddle A V P)).comp
      (Cochain.ofHom ((α_ U V P).inv ≫ c ▷ P)) (add_zero 1) := by
  simpa only [← eraseMiddle_eq_tensorLeft] using
    tensorJoin_cochain_naturality U V W (epsilonComplex A ⊗ P) P c 1 (eraseHead A P)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureHead

/-! ## ErasureHeadNaturality（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureHeadNaturality.lean） -/

/-! # 左端・中間ε消去の右因子のchain mapに関する自然性 -/

@[expose] public section ErasureHeadNaturality
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

lemma eraseHead_naturality (P Q : Complex A) (f : P ⟶ Q) :
    (Cochain.ofHom ((epsilonComplex A) ◁ f)).comp (eraseHead A Q) (zero_add 1) =
      (eraseHead A P).comp (Cochain.ofHom f) (add_zero 1) := by
  have h := tensorCochain_interchange (epsilonComplex A) (𝟙_ (Complex A)) P Q
    1 0 1 (add_zero 1) (zero_add 1) (eraseEpsilon A) (Cochain.ofHom f)
  simp only [mul_zero, Int.negOnePow_zero, one_smul, tensorLeftHom_ofHom] at h
  change (eraseRightTensor A P).comp (Cochain.ofHom ((𝟙_ (Complex A)) ◁ f)) (add_zero 1) =
    (Cochain.ofHom ((epsilonComplex A) ◁ f)).comp (eraseRightTensor A Q) (zero_add 1) at h
  rw [eraseHead, eraseHead, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← h,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    leftUnitor_naturality]

lemma eraseMiddle_naturality (K P Q : Complex A) (f : P ⟶ Q) :
    (Cochain.ofHom (K ◁ ((epsilonComplex A) ◁ f))).comp (eraseMiddle A K Q) (zero_add 1) =
      (eraseMiddle A K P).comp (Cochain.ofHom (K ◁ f)) (add_zero 1) := by
  rw [eraseMiddle_eq_tensorLeft, eraseMiddle_eq_tensorLeft,
    ← tensorLeftHom_ofHom K _ _ ((epsilonComplex A) ◁ f),
    ← tensorLeftHom_ofHom K _ _ f,
    ← tensorLeftHom_cochain_comp, ← tensorLeftHom_cochain_comp, eraseHead_naturality]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureHeadNaturality

/-! ## ErasureHeadCochainNaturality（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureHeadCochainNaturality.lean） -/

/-! # 閉性を仮定しない次数0 cochainに対するε消去の自然性 -/

@[expose] public section ErasureHeadCochainNaturality
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

lemma eraseHead_cochain_zero (P Q : Complex A) (f : Cochain P Q 0) :
    ((tensorLeftHom (epsilonComplex A) P Q).f 0 f).comp (eraseHead A Q) (zero_add 1) =
      (eraseHead A P).comp f (add_zero 1) := by
  have h := tensorCochain_interchange (epsilonComplex A) (𝟙_ (Complex A)) P Q
    1 0 1 (add_zero 1) (zero_add 1) (eraseEpsilon A) f
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  change (eraseRightTensor A P).comp ((tensorLeftHom (𝟙_ (Complex A)) P Q).f 0 f)
      (add_zero 1) =
    ((tensorLeftHom (epsilonComplex A) P Q).f 0 f).comp (eraseRightTensor A Q) (zero_add 1) at h
  rw [eraseHead, eraseHead, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← h,
    Cochain.comp_assoc_of_third_is_zero_cochain, leftUnitor_hom_cochain,
    ← Cochain.comp_assoc_of_second_is_zero_cochain]

lemma eraseMiddle_cochain_zero (K P Q : Complex A) (f : Cochain P Q 0) :
    ((tensorLeftHom K (epsilonComplex A ⊗ P) (epsilonComplex A ⊗ Q)).f 0
      ((tensorLeftHom (epsilonComplex A) P Q).f 0 f)).comp (eraseMiddle A K Q) (zero_add 1) =
    (eraseMiddle A K P).comp ((tensorLeftHom K P Q).f 0 f) (add_zero 1) := by
  rw [eraseMiddle_eq_tensorLeft, eraseMiddle_eq_tensorLeft,
    ← tensorLeftHom_cochain_comp, ← tensorLeftHom_cochain_comp, eraseHead_cochain_zero]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureHeadCochainNaturality

/-! ## ErasureTensorRight（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureTensorRight.lean） -/

/-! # ε消去と右tensor・括弧変更の整合性 -/

@[expose] public section ErasureTensorRight
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 左端εの消去は右tensorを追加してもassociatorを通じて一致する。 -/
lemma eraseHead_tensorRight (P Q : Complex A) :
    (tensorRightHom Q (epsilonComplex A ⊗ P) P).f 1 (eraseHead A P) =
    (Cochain.ofHom (α_ (epsilonComplex A) P Q).hom).comp
      (eraseHead A (P ⊗ Q)) (zero_add 1) := by
  have hunit : (α_ (𝟙_ (Complex A)) P Q).hom ≫ (λ_ (P ⊗ Q)).hom =
      (λ_ P).hom ▷ Q := by monoidal
  have h := associator_hom_cochain_left (epsilonComplex A) (𝟙_ (Complex A)) P Q 1
    (eraseEpsilon A)
  change ((tensorRightHom Q (epsilonComplex A ⊗ P) ((𝟙_ (Complex A)) ⊗ P)).f 1
    (eraseRightTensor A P)).comp (Cochain.ofHom (α_ (𝟙_ (Complex A)) P Q).hom)
      (add_zero 1) =
    (Cochain.ofHom (α_ (epsilonComplex A) P Q).hom).comp
      (eraseRightTensor A (P ⊗ Q)) (zero_add 1) at h
  rw [eraseHead, tensorRightHom_cochain_comp, tensorRightHom_ofHom]
  rw [← hunit, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_second_is_zero_cochain, h,
    Cochain.comp_assoc_of_first_is_zero_cochain]
  rfl

/-- 中間ε消去と二段階の括弧変更の整合式。 -/
lemma eraseMiddle_tensorRight (K P Q : Complex A) :
    (Cochain.ofHom ((α_ K (epsilonComplex A ⊗ P) Q).hom ≫
      K ◁ (α_ (epsilonComplex A) P Q).hom)).comp
        (eraseMiddle A K (P ⊗ Q)) (zero_add 1) =
    ((tensorRightHom Q (K ⊗ (epsilonComplex A ⊗ P)) (K ⊗ P)).f 1
      (eraseMiddle A K P)).comp (Cochain.ofHom (α_ K P Q).hom) (add_zero 1) := by
  rw [eraseMiddle_eq_tensorLeft, eraseMiddle_eq_tensorLeft]
  rw [associator_hom_cochain_middle, eraseHead_tensorRight,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureTensorRight

/-! ## ErasureTensorTransport（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureTensorTransport.lean） -/

/-! # 右tensor後の括弧変更・後方chain mapと先頭ε消去 -/

@[expose] public section ErasureTensorTransport
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 後方tensorのchain mapを適用してからのε消去を、先のε消去へ移す。 -/
lemma eraseMiddle_tensorRight_naturality (K P Q T : Complex A) (f : P ⊗ Q ⟶ T) :
    (Cochain.ofHom ((α_ K (epsilonComplex A ⊗ P) Q).hom ≫
      K ◁ (α_ (epsilonComplex A) P Q).hom ≫ K ◁ ((epsilonComplex A) ◁ f))).comp
        (eraseMiddle A K T) (zero_add 1) =
    ((tensorRightHom Q (K ⊗ (epsilonComplex A ⊗ P)) (K ⊗ P)).f 1
      (eraseMiddle A K P)).comp
        (Cochain.ofHom ((α_ K P Q).hom ≫ K ◁ f)) (add_zero 1) := by
  rw [← Category.assoc, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain, eraseMiddle_naturality,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    eraseMiddle_tensorRight, Cochain.comp_assoc_of_second_is_zero_cochain,
    ← Cochain.ofHom_comp]


end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureTensorTransport

/-! ## ErasureFirstEvaluation（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureFirstEvaluation.lean） -/

/-! # 先頭ε消去の標準生成元での成分式 -/

@[expose] public section ErasureFirstEvaluation
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 先頭εを消すと、(-1)^i倍の先頭Hom合成になる。 -/
lemma eraseFirst_generator {S : Set D} (c : S) (w : Word S) (x y : D)
    (i j b a n : ℤ) (hb : (-1) + j = b) (ha : i + b = a) (hn : a + 1 = n)
    (f : (homObject A D x c.val).X i) (z : (term A D w c.val y).X j) :
    (eraseFirst A D c w x y).v a n hn
      (ιTensorObj (homObject A D x c.val) (epsilonComplex A ⊗ term A D w c.val y) i b a ha
        (f ⊗ₜ[A] ιTensorObj (epsilonComplex A) (term A D w c.val y) (-1) j b hb
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] z))) =
    i.negOnePow • (prependMap A D w x c.val y).f n
      (ιTensorObj (homObject A D x c.val) (term A D w c.val y) i j n (by omega)
        (f ⊗ₜ[A] z)) := by
  rw [eraseFirst, cochain_comp_ofHom_apply]
  exact (congrArg (fun t => (prependMap A D w x c.val y).f n t)
    (eraseMiddle_generator A (homObject A D x c.val) (term A D w c.val y)
      i j b a n hb ha hn f z)).trans
    (chain_units_smul (prependMap A D w x c.val y) n i.negOnePow _)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureFirstEvaluation
