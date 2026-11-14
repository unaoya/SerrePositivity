module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Quotient.Append
public import SerrePositivity.DifferentialGraded.Quotient.Scalar
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Quotient.Erasure
public import SerrePositivity.DifferentialGraded.Quotient.Path.Construction
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin
public import SerrePositivity.DifferentialGraded.Category.Basic



public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
# Quotient.Composition

## 概要
17 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## CompositionErasure（旧 SerrePositivity/DifferentialGraded/Quotient/CompositionErasure.lean） -/

/-! # 全path合成のε消去Leibniz則 -/

@[expose] public section CompositionErasure
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全path直和の内部合成はε消去作用素に関してもLeibniz則を満たす。 -/
lemma internalComposition_erasure (S : Set D) (x y z : D) :
    (Cochain.ofHom (internalComposition A D S x y z)).comp (erasure A D S x z)
      (zero_add 1) =
    ((tensorRightHom (internalHom A D S y z) (internalHom A D S x y)
      (internalHom A D S x y)).f 1 (erasure A D S x y)).comp
      (Cochain.ofHom (internalComposition A D S x y z)) (add_zero 1) +
    ((tensorLeftHom (internalHom A D S x y) (internalHom A D S y z)
      (internalHom A D S y z)).f 1 (erasure A D S y z)).comp
      (Cochain.ofHom (internalComposition A D S x y z)) (add_zero 1) := by
  apply tensorRightPathCochain_ext A D S x y (internalHom A D S y z) 1
  intro w
  have hl : (Cochain.ofHom (ι A D S x y w ▷ internalHom A D S y z)).comp
      ((tensorRightHom (internalHom A D S y z) (internalHom A D S x y)
        (internalHom A D S x y)).f 1 (erasure A D S x y)) (zero_add 1) =
      (tensorRightHom (internalHom A D S y z) (term A D w x y)
        (internalHom A D S x y)).f 1 (eraseRow A D w x y) := by
    rw [← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp, erasure_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    internalComposition_left_ι]
  rw [Cochain.comp_add _ _ _ (zero_add 1),
    ← Cochain.comp_assoc_of_first_is_zero_cochain, hl,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_cochain_naturality,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    internalComposition_left_ι]
  exact appendRight_erasure A D w x y z

end SerrePositivity.DifferentialGraded.DGQuotient
end

end CompositionErasure

/-! ## InternalAssociativity（旧 SerrePositivity/DifferentialGraded/Quotient/InternalAssociativity.lean） -/

/-! # 内部全path合成の結合則 -/

@[expose] public section InternalAssociativity
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma internalComposition_assoc (S : Set D) (x y z t : D) :
    (internalComposition A D S x y z ▷ internalHom A D S z t) ≫
      internalComposition A D S x z t =
    (α_ (internalHom A D S x y) (internalHom A D S y z) (internalHom A D S z t)).hom ≫
      internalHom A D S x y ◁ internalComposition A D S y z t ≫
        internalComposition A D S x y t := by
  apply tensorRightTwoCoproduct_hom_ext (fun w : Word S => term A D w x y)
    (internalHom A D S y z) (internalHom A D S z t) (internalHom A D S x t)
  intro w
  change ((ι A D S x y w ▷ internalHom A D S y z) ▷ internalHom A D S z t) ≫
      (internalComposition A D S x y z ▷ internalHom A D S z t) ≫
        internalComposition A D S x z t = _
  rw [← comp_whiskerRight_assoc, internalComposition_left_ι,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  change (appendRight A D w x y z ▷ internalHom A D S z t) ≫
      internalComposition A D S x z t =
    (α_ (term A D w x y) (internalHom A D S y z) (internalHom A D S z t)).hom ≫
      (term A D w x y) ◁ internalComposition A D S y z t ≫
        (ι A D S x y w ▷ internalHom A D S y t) ≫ internalComposition A D S x y t
  rw [internalComposition_left_ι, appendRight_assoc]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end InternalAssociativity

/-! ## ErasureFirstTailInterchange（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureFirstTailInterchange.lean） -/

/-! # 先頭εと非隣接の後方εの消去順序の交換

隣り合う二つのεの場合は、豊穣合成の結合則を用いる別の証明が必要。
-/

@[expose] public section ErasureFirstTailInterchange
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 先頭εと、それに隣接しない後方εの二重消去は反交換する。 -/
lemma eraseFirst_tail_anticommute {S : Set D} (b c : S) (w : Word S) (i : ℕ) (x y : D) :
    (eraseFirst A D b (c :: w) x y).comp
      (eraseFace A D (c :: w) (i + 1) x y) (show (1 : ℤ) + 1 = 2 by omega) =
    -((eraseFace A D (b :: c :: w) (i + 2) x y).comp
      (eraseFirst A D b ((c :: w).eraseIdx (i + 1)) x y)
      (show (1 : ℤ) + 1 = 2 by omega)) := by
  rw [eraseFirst, eraseFirst, Cochain.comp_assoc_of_second_is_zero_cochain,
    prependMap_eraseFace_succ, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    eraseMiddle_tail_anticommute, Cochain.neg_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureFirstTailInterchange

/-! ## ErasureAdjacentInterchange（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureAdjacentInterchange.lean） -/

/-! # 隣接する先頭二つのεの二重消去の反交換 -/

@[expose] public section ErasureAdjacentInterchange
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma eraseFirst_adjacent_anticommute {S : Set D} (b c : S) (w : Word S) (x y : D) :
    (eraseFirst A D b (c :: w) x y).comp
      (eraseFirst A D c w x y) (show (1 : ℤ) + 1 = 2 by omega) =
    -((eraseFace A D (b :: c :: w) 1 x y).comp
      (eraseFirst A D b w x y) (show (1 : ℤ) + 1 = 2 by omega)) := by
  change ((eraseMiddle A (homObject A D x b.val) (term A D (c :: w) b.val y)).comp
    (Cochain.ofHom (prependMap A D (c :: w) x b.val y)) (add_zero 1)).comp
      (eraseFirst A D c w x y) (by omega) =
    -((eraseFace A D (b :: c :: w) 1 x y).comp
      ((eraseMiddle A (homObject A D x b.val) (term A D w b.val y)).comp
        (Cochain.ofHom (prependMap A D w x b.val y)) (add_zero 1)) (by omega))
  rw [Cochain.comp_assoc_of_second_is_zero_cochain,
    prependMap_eraseFirst, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    eraseMiddle_tail_anticommute, Cochain.neg_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain]
  rfl

/-- 先頭εと任意の後方位置の消去は反交換する。範囲外の位置も含む。 -/
lemma eraseFirst_face_anticommute {S : Set D} (b : S) (w : Word S) (i : ℕ) (x y : D) :
    (eraseFirst A D b w x y).comp (eraseFace A D w i x y)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -((eraseFace A D (b :: w) (i + 1) x y).comp
      (eraseFirst A D b (w.eraseIdx i) x y) (show (1 : ℤ) + 1 = 2 by omega)) := by
  cases w with
  | nil =>
    simp only [eraseFace_cons_succ, eraseFace_nil, map_zero,
      Cochain.comp_zero, Cochain.zero_comp, neg_zero]
  | cons c w =>
    cases i with
    | zero => exact eraseFirst_adjacent_anticommute A D b c w x y
    | succ i => exact eraseFirst_tail_anticommute A D b c w i x y

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureAdjacentInterchange

/-! ## DoubleFaces（旧 SerrePositivity/DifferentialGraded/Quotient/DoubleFaces.lean） -/

/-! # 終域の語を保持した二重ε消去

消去後の語とcochainを依存対で保持し、異なる消去順序の終域を同時に比較する。
-/

@[expose] public section DoubleFaces
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 終域の語付き次数2 cochain。 -/
def DoubleFace {S : Set D} (w : Word S) (x y : D) :=
  Σ z : Word S, Cochain (term A D w x y) (term A D z x y) 2

/-- 二つの位置を順に消し、終域の語も保持する。 -/
def doubleFace {S : Set D} (w : Word S) (i j : ℕ) (x y : D) : DoubleFace A D w x y :=
  ⟨(w.eraseIdx i).eraseIdx j,
    (eraseFace A D w i x y).comp (eraseFace A D (w.eraseIdx i) j x y) (by omega)⟩

/-- 終域の語を変えずcochainを負にする。 -/
def negateDoubleFace {S : Set D} {w : Word S} {x y : D} :
    DoubleFace A D w x y → DoubleFace A D w x y
  | ⟨z, f⟩ => ⟨z, -f⟩

lemma negateDoubleFace_involutive {S : Set D} {w : Word S} {x y : D}
    (f : DoubleFace A D w x y) : negateDoubleFace A D (negateDoubleFace A D f) = f := by
  rcases f with ⟨z, f⟩
  simp only [negateDoubleFace, neg_neg]

/-- 前方Homとεを残して次数2 cochainをtensorする。 -/
def prefixDoubleFace {S : Set D} (b : S) (w : Word S) (x y : D) :
    DoubleFace A D w b.val y → DoubleFace A D (b :: w) x y
  | ⟨z, f⟩ => ⟨b :: z,
      (tensorLeftHom (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        (epsilonComplex A ⊗ term A D z b.val y)).f 2
        ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
          (term A D z b.val y)).f 2 f)⟩

lemma prefixDoubleFace_negate {S : Set D} (b : S) (w : Word S) (x y : D)
    (f : DoubleFace A D w b.val y) :
    prefixDoubleFace A D b w x y (negateDoubleFace A D f) =
      negateDoubleFace A D (prefixDoubleFace A D b w x y f) := by
  rcases f with ⟨z, f⟩
  simp only [prefixDoubleFace, negateDoubleFace, map_neg]

lemma doubleFace_cons_succ {S : Set D} (b : S) (w : Word S) (i j : ℕ) (x y : D) :
    doubleFace A D (b :: w) (i + 1) (j + 1) x y =
      prefixDoubleFace A D b w x y (doubleFace A D w i j b.val y) := by
  exact congrArg (fun f => (⟨b :: (w.eraseIdx i).eraseIdx j, f⟩ :
    DoubleFace A D (b :: w) x y)) (eraseFace_succ_comp A D b w i j x y)

lemma doubleFace_cons_zero {S : Set D} (b : S) (w : Word S) (j : ℕ) (x y : D) :
    doubleFace A D (b :: w) 0 j x y =
      negateDoubleFace A D (doubleFace A D (b :: w) (j + 1) 0 x y) := by
  exact congrArg (fun f => (⟨w.eraseIdx j, f⟩ : DoubleFace A D (b :: w) x y))
    (eraseFirst_face_anticommute A D b w j x y)

/-- 異なる二つの元の位置を消す順序の交換は、終域の語も含めて反交換する。 -/
lemma doubleFace_swap_of_le {S : Set D} (w : Word S) (i j : ℕ) (hij : i ≤ j) (x y : D) :
    doubleFace A D w i j x y =
      negateDoubleFace A D (doubleFace A D w (j + 1) i x y) := by
  induction w generalizing i j x y with
  | nil => simp only [doubleFace, List.eraseIdx_nil, eraseFace_nil,
      Cochain.zero_comp, negateDoubleFace, neg_zero]
  | cons b w ih =>
    cases i with
    | zero => exact doubleFace_cons_zero A D b w j x y
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        rw [doubleFace_cons_succ, doubleFace_cons_succ, ← prefixDoubleFace_negate]
        exact congrArg (prefixDoubleFace A D b w x y) (ih i j (by omega) b.val y)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DoubleFaces

/-! ## DoubleFaceSum（旧 SerrePositivity/DifferentialGraded/Quotient/DoubleFaceSum.lean） -/

/-! # 二重消去を全path直和へ入れた項の反交換 -/

@[expose] public section DoubleFaceSum
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 終域の語付きcochainを全path直和へ入れる。 -/
def includeDoubleFace {S : Set D} {w : Word S} {x y : D} :
    DoubleFace A D w x y → Cochain (term A D w x y) (internalHom A D S x y) 2
  | ⟨z, f⟩ => f.comp (Cochain.ofHom (ι A D S x y z)) (add_zero 2)

lemma includeDoubleFace_negate {S : Set D} {w : Word S} {x y : D}
    (f : DoubleFace A D w x y) :
    includeDoubleFace A D (negateDoubleFace A D f) = -includeDoubleFace A D f := by
  rcases f with ⟨z, f⟩
  simp only [includeDoubleFace, negateDoubleFace, Cochain.neg_comp]

/-- 二重消去をその終域のpath包含と合成した項。 -/
def erasurePair {S : Set D} (w : Word S) (i j : ℕ) (x y : D) :
    Cochain (term A D w x y) (internalHom A D S x y) 2 :=
  includeDoubleFace A D (doubleFace A D w i j x y)

lemma erasurePair_swap_of_le {S : Set D} (w : Word S) (i j : ℕ) (hij : i ≤ j) (x y : D) :
    erasurePair A D w i j x y = -erasurePair A D w (j + 1) i x y := by
  exact (congrArg (includeDoubleFace A D) (doubleFace_swap_of_le A D w i j hij x y)).trans
    (includeDoubleFace_negate A D _)

/-- 有限和相殺の対合が、実際の二重消去項を負にする。 -/
lemma erasurePair_swap {S : Set D} (w : Word S) (i j : ℕ) (x y : D) :
    erasurePair A D w i j x y =
      -erasurePair A D w (swapErasure (i, j)).1 (swapErasure (i, j)).2 x y := by
  by_cases hij : j < i
  · have h := erasurePair_swap_of_le A D w j (i - 1) (by omega) x y
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at h
    simp only [swapErasure, ite_eq_left hij]
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  · simpa only [swapErasure, Prod.fst, Prod.snd, ite_eq_right hij] using
      erasurePair_swap_of_le A D w i j (by omega) x y

lemma erasurePair_double_sum_zero {S : Set D} (w : Word S) (x y : D) :
    ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range (w.length - 1),
      erasurePair A D w i j x y = 0 :=
  erasure_double_sum_cancel w.length (fun i j => erasurePair A D w i j x y)
    (fun i _ j _ => erasurePair_swap A D w i j x y)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DoubleFaceSum

/-! ## ErasureSquare（旧 SerrePositivity/DifferentialGraded/Quotient/ErasureSquare.lean） -/

/-! # 全path直和のε消去作用素の二乗零 -/

@[expose] public section ErasureSquare
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 作用素の二乗を各pathへ制限すると、全ての二重消去項の有限二重和になる。 -/
lemma erasure_square_precomp_double_sum (S : Set D) (x y : D) (w : Word S) :
    (Cochain.ofHom (ι A D S x y w)).comp
      ((erasure A D S x y).comp (erasure A D S x y) (show (1 : ℤ) + 1 = 2 by omega))
      (zero_add 2) =
    ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range (w.length - 1),
      erasurePair A D w i j x y := by
  rw [erasure_square_precomp]
  apply Finset.sum_congr rfl
  intro i hi
  let R : Cochain (term A D (w.eraseIdx i) x y) (internalHom A D S x y) 1 →+
      Cochain (term A D w x y) (internalHom A D S x y) 2 :=
    { toFun := fun f => (eraseFace A D w i x y).comp f (by omega)
      map_zero' := Cochain.comp_zero _ _
      map_add' := fun f g => Cochain.comp_add _ f g _ }
  change R (eraseRow A D (w.eraseIdx i) x y) = _
  rw [eraseRow, map_sum, List.length_eraseIdx_of_lt (Finset.mem_range.mp hi)]
  apply Finset.sum_congr rfl
  intro j _
  change (eraseFace A D w i x y).comp
      ((eraseFace A D (w.eraseIdx i) j x y).comp
        (Cochain.ofHom (ι A D S x y ((w.eraseIdx i).eraseIdx j))) (add_zero 1))
      (show (1 : ℤ) + 1 = 2 by omega) =
    ((eraseFace A D w i x y).comp (eraseFace A D (w.eraseIdx i) j x y)
      (show (1 : ℤ) + 1 = 2 by omega)).comp
        (Cochain.ofHom (ι A D S x y ((w.eraseIdx i).eraseIdx j))) (add_zero 2)
  exact (Cochain.comp_assoc_of_third_is_zero_cochain _ _ _ _).symm

/-- 全path直和のε消去作用素は二乗零である。 -/
lemma erasure_square_zero (S : Set D) (x y : D) :
    (erasure A D S x y).comp (erasure A D S x y) (show (1 : ℤ) + 1 = 2 by omega) = 0 := by
  apply pathCochain_ext A D S x y 2
  intro w
  rw [erasure_square_precomp_double_sum, erasurePair_double_sum_zero, Cochain.comp_zero]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ErasureSquare

/-! ## Differential（旧 SerrePositivity/DifferentialGraded/Quotient/Differential.lean） -/

/-! # 明示的dg商の最終Hom微分

全path直和の内部微分にε消去作用素を加える。内部微分との反交換と消去作用素の二乗零は
既に証明済みであり、条件を外部から仮定せずに非有界複体を構成する。
合成がこの微分と両立することは後続で検証する。
-/

@[expose] public section Differential
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 内部微分とε消去の和を微分とする、最終dg商のHom複体。 -/
def quotientHom (S : Set D) (x y : D) : Complex A :=
  perturbComplex (internalHom A D S x y) (erasure A D S x y)
    (erasure_closed A D S x y) (erasure_square_zero A D S x y)

@[simp] lemma quotientHom_X (S : Set D) (x y : D) (i : ℤ) :
    (quotientHom A D S x y).X i = (internalHom A D S x y).X i := rfl

@[simp] lemma quotientHom_d (S : Set D) (x y : D) (i : ℤ) :
    (quotientHom A D S x y).d i (i + 1) =
      (internalHom A D S x y).d i (i + 1) + (erasure A D S x y).v i (i + 1) rfl :=
  perturbComplex_d _ _ _ _ _

/-- 空pathの包含は最終微分に関してもchain mapとなる。 -/
def originalHomInclusion (S : Set D) (x y : D) :
    homObject A D x y ⟶ quotientHom A D S x y :=
  CochainComplex.ofHom (fun i => (originalHom A D S x y).f i) (fun i => by
    have hz : (originalHom A D S x y).f i ≫ (erasure A D S x y).v i (i + 1) rfl = 0 := by
      simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] using
        congrArg (fun f : Cochain (homObject A D x y) (internalHom A D S x y) 1 =>
          f.v i (i + 1) rfl) (erasure_originalHom A D S x y)
    rw [quotientHom_d, comp_add, hz, add_zero]
    exact (originalHom A D S x y).comm i (i + 1))

@[simp] lemma originalHomInclusion_f (S : Set D) (x y : D) (i : ℤ) :
    (originalHomInclusion A D S x y).f i = (originalHom A D S x y).f i := rfl

/-- 空部分圏のとき消去作用素は全体で零。 -/
lemma erasure_empty (x y : D) : erasure A D ∅ x y = 0 := by
  apply pathCochain_ext A D ∅ x y 1
  intro w
  have hw := word_empty w
  subst w
  rw [erasure_precomp, eraseRow_nil, Cochain.comp_zero]

/-- 空部分圏を殺す最終Hom複体は、元のHom複体と同型である。 -/
def quotientHom_emptyIso (x y : D) : homObject A D x y ≅ quotientHom A D ∅ x y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i).mapIso
      (emptyHomIso A D x y)) (fun i j hij => by
        change (originalHom A D ∅ x y).f i ≫ (quotientHom A D ∅ x y).d i j =
          (homObject A D x y).d i j ≫ (originalHom A D ∅ x y).f j
        change i + 1 = j at hij
        subst j
        rw [quotientHom_d, erasure_empty, Cochain.zero_v, add_zero]
        exact (originalHom A D ∅ x y).comm i (i + 1))

lemma quotientHom_emptyIso_hom (x y : D) :
    (quotientHom_emptyIso A D x y).hom = originalHomInclusion A D ∅ x y := by
  apply HomologicalComplex.Hom.ext
  funext i
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end Differential

/-! ## EpsilonElement（旧 SerrePositivity/DifferentialGraded/Quotient/EpsilonElement.lean） -/

/-! # 商の指定次数−1生成元と単一pathの成分 -/

@[expose] public section EpsilonElement
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma epsilonTerm_generator {S : Set D} (b : S) :
    (epsilonTerm A D b).f (-1)
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) =
    ιTensorObj (homObject A D b.val b.val)
      (epsilonComplex A ⊗ homObject A D b.val b.val) 0 (-1) (-1) (by omega)
      ((unitElement A b.val).val ⊗ₜ[A]
        ιTensorObj (epsilonComplex A) (homObject A D b.val b.val) (-1) 0 (-1) (by omega)
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A]
            (unitElement A b.val).val)) := by
  exact unitSandwich_apply (homObject A D b.val b.val) (epsilonComplex A)
    (eId (Complex A) b.val) (-1)
    ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))

variable [Small.{u} D]
/-- 指定対象の次数−1のpath生成元。最終微分について閉じているとは主張しない。 -/
def epsilonElement (S : Set D) (b : S) : (quotientHom A D S b.val b.val).X (-1) :=
  (epsilon A D S b).f (-1)
    ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))

end SerrePositivity.DifferentialGraded.DGQuotient
end

end EpsilonElement

/-! ## PrependDifferential（旧 SerrePositivity/DifferentialGraded/Quotient/PrependDifferential.lean） -/

/-! # 最終Hom微分に関する先頭Hom作用

内部chain mapとε消去の基底Leibniz則を加えて、元のHomと最終path Homのtensorから
最終path Homへの実際のchain mapを構成する。
-/

@[expose] public section PrependDifferential
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 空pathを左に置く合成の、最終微分についてのLeibniz則。 -/
lemma internalPrepend_total_d_apply (S : Set D) (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (homObject A D x y).X p) (b : (internalHom A D S y z).X q) :
    (quotientHom A D S x z).d n (n + 1)
      ((internalPrepend A D S x y z).f n
        (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    (internalPrepend A D S x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) (p + 1) q (n + 1)
        (by omega) ((homObject A D x y).d p (p + 1) a ⊗ₜ[A] b)) +
    p.negOnePow • (internalPrepend A D S x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (quotientHom A D S y z).d q (q + 1) b)) := by
  have hi := ConcreteCategory.congr_hom ((internalPrepend A D S x y z).comm n (n + 1))
    (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))
  change (internalHom A D S x z).d n (n + 1) (_ : (internalHom A D S x z).X n) =
    (internalPrepend A D S x y z).f (n + 1)
      ((homObject A D x y ⊗ internalHom A D S y z).d n (n + 1)
        (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) at hi
  have hd := SerrePositivity.cochainTensor_d_apply_ι
    (homObject A D x y) (internalHom A D S y z) p q n hn a b
  have hi' := hi.trans (congrArg (fun v :
      (homObject A D x y ⊗ internalHom A D S y z).X (n + 1) =>
    (internalPrepend A D S x y z).f (n + 1) v) hd)
  clear hi
  have hi := hi'
  rw [map_add, chain_units_smul] at hi
  rw [quotientHom_d, quotientHom_d]
  change (internalHom A D S x z).d n (n + 1)
      ((internalPrepend A D S x y z).f n
        (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) +
      (erasure A D S x z).v n (n + 1) rfl
        ((internalPrepend A D S x y z).f n
          (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    (internalPrepend A D S x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) (p + 1) q (n + 1)
        (by omega) ((homObject A D x y).d p (p + 1) a ⊗ₜ[A] b)) +
    p.negOnePow • (internalPrepend A D S x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] ((internalHom A D S y z).d q (q + 1) b +
          (erasure A D S y z).v q (q + 1) rfl b)))
  exact (congrArg₂ (· + ·) hi (internalPrepend_erasure_apply A D S x y z p q n hn a b)).trans (by
    simp only [TensorProduct.tmul_add, map_add, smul_add]
    abel)

/-- 元のHomは最終Hom複体へ先頭から作用する。これは最終微分に関するchain map。 -/
def quotientPrepend (S : Set D) (x y z : D) :
    homObject A D x y ⊗ quotientHom A D S y z ⟶ quotientHom A D S x z :=
  tensorLift (fun i j n h =>
    ιTensorObj (homObject A D x y) (internalHom A D S y z) i j n h ≫
      (internalPrepend A D S x y z).f n) (fun i j => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro a b
        exact internalPrepend_total_d_apply A D S x y z i j (i + j) rfl a b)

lemma quotientPrepend_ι (S : Set D) (x y z : D) (i j n : ℤ) (hn : i + j = n) :
    ιTensorObj (homObject A D x y) (quotientHom A D S y z) i j n hn ≫
      (quotientPrepend A D S x y z).f n =
    ιTensorObj (homObject A D x y) (internalHom A D S y z) i j n hn ≫
      (internalPrepend A D S x y z).f n :=
  ι_tensorLift _ _ i j n hn

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PrependDifferential

/-! ## CompositionDifferential（旧 SerrePositivity/DifferentialGraded/Quotient/CompositionDifferential.lean） -/

/-! # 全pathの最終Hom微分に関する合成 -/

@[expose] public section CompositionDifferential
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全消去Leibniz則の斉次成分。右の消去項の符号は左の次数p。 -/
lemma internalComposition_erasure_apply (S : Set D) (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (internalHom A D S x y).X p) (b : (internalHom A D S y z).X q) :
    (erasure A D S x z).v n (n + 1) rfl
      ((internalComposition A D S x y z).f n
        (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    (internalComposition A D S x y z).f (n + 1)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) (p + 1) q (n + 1)
        (by omega) ((erasure A D S x y).v p (p + 1) rfl a ⊗ₜ[A] b)) +
    p.negOnePow • (internalComposition A D S x y z).f (n + 1)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (erasure A D S y z).v q (q + 1) rfl b)) := by
  have h := congrArg (fun f : Cochain
      (internalHom A D S x y ⊗ internalHom A D S y z) (internalHom A D S x z) 1 =>
    f.v n (n + 1) rfl
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b)))
    (internalComposition_erasure A D S x y z)
  simp only [Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply] at h
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply, cochain_comp_ofHom_apply,
    tensorRightHom_apply, tensorLeftHom_apply, chain_units_smul] at h
  simpa only [one_mul] using h

/-- 最終Homの全微分についてのLeibniz則。 -/
lemma internalComposition_total_d_apply (S : Set D) (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (internalHom A D S x y).X p) (b : (internalHom A D S y z).X q) :
    (quotientHom A D S x z).d n (n + 1)
      ((internalComposition A D S x y z).f n
        (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    (internalComposition A D S x y z).f (n + 1)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) (p + 1) q (n + 1)
        (by omega) ((quotientHom A D S x y).d p (p + 1) a ⊗ₜ[A] b)) +
    p.negOnePow • (internalComposition A D S x y z).f (n + 1)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (quotientHom A D S y z).d q (q + 1) b)) := by
  have hi := ConcreteCategory.congr_hom ((internalComposition A D S x y z).comm n (n + 1))
    (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))
  change (internalHom A D S x z).d n (n + 1) (_ : (internalHom A D S x z).X n) =
    (internalComposition A D S x y z).f (n + 1)
      ((internalHom A D S x y ⊗ internalHom A D S y z).d n (n + 1)
        (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) at hi
  have hd := SerrePositivity.cochainTensor_d_apply_ι
    (internalHom A D S x y) (internalHom A D S y z) p q n hn a b
  have hi' := hi.trans (congrArg (fun v :
      (internalHom A D S x y ⊗ internalHom A D S y z).X (n + 1) =>
    (internalComposition A D S x y z).f (n + 1) v) hd)
  clear hi
  have hi := hi'
  rw [map_add, chain_units_smul] at hi
  rw [quotientHom_d, quotientHom_d, quotientHom_d]
  change (internalHom A D S x z).d n (n + 1)
      ((internalComposition A D S x y z).f n
        (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) +
      (erasure A D S x z).v n (n + 1) rfl
        ((internalComposition A D S x y z).f n
          (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    (internalComposition A D S x y z).f (n + 1)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) (p + 1) q (n + 1)
        (by omega) (((internalHom A D S x y).d p (p + 1) a +
          (erasure A D S x y).v p (p + 1) rfl a) ⊗ₜ[A] b)) +
    p.negOnePow • (internalComposition A D S x y z).f (n + 1)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] ((internalHom A D S y z).d q (q + 1) b +
          (erasure A D S y z).v q (q + 1) rfl b)))
  exact (congrArg₂ (· + ·) hi
    (internalComposition_erasure_apply A D S x y z p q n hn a b)).trans (by
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, smul_add]
    abel)

/-- 全pathの最終Hom複体間の合成。最終微分に関する実際のchain map。 -/
def quotientComposition (S : Set D) (x y z : D) :
    quotientHom A D S x y ⊗ quotientHom A D S y z ⟶ quotientHom A D S x z :=
  tensorLift (fun i j n h =>
    ιTensorObj (internalHom A D S x y) (internalHom A D S y z) i j n h ≫
      (internalComposition A D S x y z).f n) (fun i j => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro a b
        exact internalComposition_total_d_apply A D S x y z i j (i + j) rfl a b)

lemma quotientComposition_ι (S : Set D) (x y z : D) (i j n : ℤ) (hn : i + j = n) :
    ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) i j n hn ≫
      (quotientComposition A D S x y z).f n =
    ιTensorObj (internalHom A D S x y) (internalHom A D S y z) i j n hn ≫
      (internalComposition A D S x y z).f n :=
  ι_tensorLift _ _ i j n hn

end SerrePositivity.DifferentialGraded.DGQuotient
end

end CompositionDifferential

/-! ## CompositionEvaluation（旧 SerrePositivity/DifferentialGraded/Quotient/CompositionEvaluation.lean） -/

/-! # 最終合成の純tensor上の直接評価 -/

@[expose] public section CompositionEvaluation
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma quotientComposition_apply (S : Set D) (x y z : D) (p q n : ℤ) (hn : p + q = n)
    (a : (quotientHom A D S x y).X p) (b : (quotientHom A D S y z).X q) :
    (quotientComposition A D S x y z).f n
      (ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) p q n hn (a ⊗ₜ[A] b)) =
    (internalComposition A D S x y z).f n
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b)) :=
  ConcreteCategory.congr_hom (quotientComposition_ι A D S x y z p q n hn) (a ⊗ₜ[A] b)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end CompositionEvaluation

/-! ## CompositionComparison（旧 SerrePositivity/DifferentialGraded/Quotient/CompositionComparison.lean） -/

/-! # 最終合成の成分と元のHom包含との比較 -/

@[expose] public section CompositionComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 微分を変えても最終合成の各次数の射は内部合成の射そのものである。 -/
lemma quotientComposition_f (S : Set D) (x y z : D) (n : ℤ) :
    (quotientComposition A D S x y z).f n = (internalComposition A D S x y z).f n := by
  apply mapBifunctor.hom_ext
  intro i j hij
  exact quotientComposition_ι A D S x y z i j n hij

/-- 最終合成は元のdg圏の豊穣合成と包含を通じて一致する。 -/
lemma quotientComposition_original (S : Set D) (x y z : D) :
    (originalHomInclusion A D S x y ⊗ₘ originalHomInclusion A D S y z) ≫
      quotientComposition A D S x y z =
    eComp (Complex A) x y z ≫ originalHomInclusion A D S x z := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, quotientComposition_f,
    HomologicalComplex.comp_f, originalHomInclusion_f]
  have h := congrArg (fun f => f.f n) (internalComposition_original_original A D S x y z)
  simp only [HomologicalComplex.comp_f] at h
  exact h

end SerrePositivity.DifferentialGraded.DGQuotient
end

end CompositionComparison

/-! ## Identity（旧 SerrePositivity/DifferentialGraded/Quotient/Identity.lean） -/

/-! # 最終Homの恒等射と合成の左単位 -/

@[expose] public section Identity
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の恒等射を最終Homへ入れた閉次数0の単位。 -/
def quotientIdentity (S : Set D) (x : D) : 𝟙_ (Complex A) ⟶ quotientHom A D S x x :=
  eId (Complex A) x ≫ originalHomInclusion A D S x x

lemma quotientIdentity_f (S : Set D) (x : D) (n : ℤ) :
    (quotientIdentity A D S x).f n = (internalIdentity A D S x).f n := rfl

lemma quotientComposition_left_unit (S : Set D) (x y : D) :
    (λ_ (quotientHom A D S x y)).inv ≫ quotientIdentity A D S x ▷ quotientHom A D S x y ≫
      quotientComposition A D S x x y = 𝟙 _ := by
  apply chain_ext_apply
  intro n a
  simp only [chain_comp_apply]
  rw [complexLeftUnitor_inv_apply, whiskerRight_apply, quotientComposition_f, quotientIdentity_f]
  have h := congrArg (fun f : internalHom A D S x y ⟶ internalHom A D S x y => f.f n a)
    (internalComposition_left_unit A D S x y)
  change (internalComposition A D S x x y).f n
    ((internalIdentity A D S x ▷ internalHom A D S x y).f n
      ((λ_ (internalHom A D S x y)).inv.f n a)) = a at h
  rw [complexLeftUnitor_inv_apply, whiskerRight_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGQuotient
end

end Identity

/-! ## RightIdentity（旧 SerrePositivity/DifferentialGraded/Quotient/RightIdentity.lean） -/

/-! # 最終Hom合成の右単位 -/

@[expose] public section RightIdentity
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma quotientComposition_right_unit (S : Set D) (x y : D) :
    (ρ_ (quotientHom A D S x y)).inv ≫ quotientHom A D S x y ◁ quotientIdentity A D S y ≫
      quotientComposition A D S x y y = 𝟙 _ := by
  apply chain_ext_apply
  intro n a
  simp only [chain_comp_apply]
  rw [complexRightUnitor_inv_apply, whiskerLeft_apply, quotientComposition_f, quotientIdentity_f]
  have h := congrArg (fun f : internalHom A D S x y ⟶ internalHom A D S x y => f.f n a)
    (internalComposition_right_unit A D S x y)
  change (internalComposition A D S x y y).f n
    ((internalHom A D S x y ◁ internalIdentity A D S y).f n
      ((ρ_ (internalHom A D S x y)).inv.f n a)) = a at h
  rw [complexRightUnitor_inv_apply, whiskerLeft_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGQuotient
end

end RightIdentity

/-! ## Associativity（旧 SerrePositivity/DifferentialGraded/Quotient/Associativity.lean） -/

/-! # 最終Hom合成の結合則 -/

@[expose] public section Associativity
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma quotientComposition_assoc (S : Set D) (x y z t : D) :
    (quotientComposition A D S x y z ▷ quotientHom A D S z t) ≫
      quotientComposition A D S x z t =
    (α_ (quotientHom A D S x y) (quotientHom A D S y z) (quotientHom A D S z t)).hom ≫
      quotientHom A D S x y ◁ quotientComposition A D S y z t ≫
        quotientComposition A D S x y t := by
  apply tensorComposition_assoc_of_apply
  intro p q r n hn a b c
  simp only [quotientComposition_apply]
  exact tensorComposition_assoc_apply
    (internalHom A D S x y) (internalHom A D S y z) (internalHom A D S z t)
    (internalHom A D S x z) (internalHom A D S y t) (internalHom A D S x t)
    (internalComposition A D S x y z) (internalComposition A D S x z t)
    (internalComposition A D S y z t) (internalComposition A D S x y t)
    (internalComposition_assoc A D S x y z t) p q r n hn a b c

end SerrePositivity.DifferentialGraded.DGQuotient
end

end Associativity

/-! ## Category（旧 SerrePositivity/DifferentialGraded/Quotient/Category.lean） -/

/-! # 明示的path商のMathlib豊穣dg圏 -/

@[expose] public section Category
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の対象と一対一に対応する商の対象。元のdg構造とのinstance衝突を避ける。 -/
structure QuotientObject (D : Type v) (S : Set D) where
  val : D

/-- 商は対象を変更しない。 -/
def quotientObjectEquiv (S : Set D) : D ≃ QuotientObject D S where
  toFun x := ⟨x⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl

/-- 最終Hom・単位・合成・三つの法則から得られる主豊穣dg構造。 -/
instance quotientDGCategory (S : Set D) : DGCategory A (QuotientObject D S) :=
  ofHomObjects A (QuotientObject D S)
    (fun x y => quotientHom A D S x.val y.val)
    (fun x => quotientIdentity A D S x.val)
    (fun x y z => quotientComposition A D S x.val y.val z.val)
    (fun x y => quotientComposition_left_unit A D S x.val y.val)
    (fun x y => quotientComposition_right_unit A D S x.val y.val)
    (fun w x y z => by
      rw [quotientComposition_assoc, Iso.inv_hom_id_assoc])

/-- 元のHomの空path包含によるdg関手。 -/
def inclusion (S : Set D) : DGFunctor A D (QuotientObject D S) where
  obj x := ⟨x⟩
  map x y := originalHomInclusion A D S x y
  map_id _x := rfl
  map_comp x y z := (quotientComposition_original A D S x y z).symm

/-- 豊穣合成の成分と通常順dg合成のKoszul比較。 -/
lemma quotientComposition_eq_signed_compose (S : Set D) (x y z : D)
    (p q n : ℤ) (hn : p + q = n)
    (f : (quotientHom A D S x y).X p) (g : (quotientHom A D S y z).X q) :
    (quotientComposition A D S x y z).f n
      (ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) p q n hn (f ⊗ₜ[A] g)) =
    (p * q).negOnePow • compose A (x := (⟨x⟩ : QuotientObject D S))
      (y := (⟨y⟩ : QuotientObject D S)) (z := (⟨z⟩ : QuotientObject D S)) g f hn :=
  forward_eq_signed_compose A (D := QuotientObject D S)
    (x := ⟨x⟩) (y := ⟨y⟩) (z := ⟨z⟩) f g hn

end SerrePositivity.DifferentialGraded.DGQuotient
end

end Category

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Drinfeld "Construction §3.1"] _root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject
attribute [cite Drinfeld "Construction §3.1"] _root_.SerrePositivity.DifferentialGraded.DGQuotient.epsilonElement
attribute [cite Drinfeld "Construction §3.1"] _root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion
