module

public import SerrePositivity.CategoryTheory.Limits
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# 有限集合の直和の構造同型

標準有限集合を二項和へ展開し、和の結合・単位・交換を再び標準有限集合へ戻す。
三つのブロックへの制限で構造射を比較するための式も整備する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.FiniteBijection

open CategoryTheory

/-- 三つのブロックの括弧を変更する全単射。 -/
def assocEquiv (m n k : ℕ) : Fin ((m + n) + k) ≃ Fin (m + (n + k)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)).trans
      ((Equiv.sumAssoc _ _ _).trans
        ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv)))

@[simp] lemma assocEquiv_first (m n k : ℕ) (i : Fin m) :
    assocEquiv m n k (Fin.castAdd k (Fin.castAdd n i)) = Fin.castAdd (n + k) i := by
  simp [assocEquiv]

@[simp] lemma assocEquiv_second (m n k : ℕ) (i : Fin n) :
    assocEquiv m n k (Fin.castAdd k (Fin.natAdd m i)) = Fin.natAdd m (Fin.castAdd k i) := by
  simp [assocEquiv]

@[simp] lemma assocEquiv_third (m n k : ℕ) (i : Fin k) :
    assocEquiv m n k (Fin.natAdd (m + n) i) = Fin.natAdd m (Fin.natAdd n i) := by
  simp [assocEquiv]

/-- 括弧の変更は、因子の順序を保つ次数の等式による移送。 -/
lemma assocEquiv_eq_finCongr (l m n : ℕ) :
    assocEquiv l m n = finCongr (Nat.add_assoc l m n) := by
  ext i
  obtain ⟨u, rfl⟩ := (finSumFinEquiv : Fin (l + m) ⊕ Fin n ≃ Fin ((l + m) + n)).surjective i
  cases u with
  | inl j =>
    obtain ⟨v, rfl⟩ := (finSumFinEquiv : Fin l ⊕ Fin m ≃ Fin (l + m)).surjective j
    cases v <;> simp [assocEquiv]
  | inr j =>
    simp [assocEquiv, Nat.add_assoc]

/-- 二つのブロックを交換する全単射。 -/
def swapEquiv (m n : ℕ) : Fin (m + n) ≃ Fin (n + m) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv)

@[simp] lemma swapEquiv_first (m n : ℕ) (i : Fin m) :
    swapEquiv m n (Fin.castAdd n i) = Fin.natAdd n i := by simp [swapEquiv]

@[simp] lemma swapEquiv_second (m n : ℕ) (i : Fin n) :
    swapEquiv m n (Fin.natAdd m i) = Fin.castAdd m i := by simp [swapEquiv]

/-- 右ブロックが空の交換は、次数の可換則による移送。 -/
lemma swapEquiv_zero_right (n : ℕ) : swapEquiv n 0 = finCongr (Nat.add_comm n 0) := by
  ext i
  obtain ⟨u, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin 0 ≃ Fin (n + 0)).surjective i
  cases u with
  | inl j => simp only [finSumFinEquiv_apply_left, swapEquiv_first]; simp
  | inr j => exact Fin.elim0 j
/-- 左ブロックが空の交換は、次数の可換則による移送。 -/
lemma swapEquiv_zero_left (n : ℕ) : swapEquiv 0 n = finCongr (Nat.add_comm 0 n) := by
  ext i
  obtain ⟨u, rfl⟩ := (finSumFinEquiv : Fin 0 ⊕ Fin n ≃ Fin (0 + n)).surjective i
  cases u with
  | inl j => exact Fin.elim0 j
  | inr j => simp only [finSumFinEquiv_apply_right, swapEquiv_second]; simp

/-- 右側の一因子とのブロック交換は、巡回置換と次数の移送の合成。 -/
lemma swapEquiv_right_one (n : ℕ) :
    swapEquiv n 1 = (finRotate (n + 1)).trans (finCongr (Nat.one_add n).symm) := by
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · change swapEquiv n 1 (Fin.natAdd n (0 : Fin 1)) = _
    rw [swapEquiv_second]
    apply Fin.ext
    simp
  · change swapEquiv n 1 (Fin.castAdd 1 j) = _
    rw [swapEquiv_first]
    apply Fin.ext
    have h : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
    simp only [Equiv.trans_apply, finCongr_apply, Fin.val_cast]
    rw [h]
    simp [Nat.add_comm]

@[simp] lemma blockEquiv_first {m n m' n' : ℕ}
    (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n') (i : Fin m) :
    blockEquiv e f (Fin.castAdd n i) = Fin.castAdd n' (e i) := by simp [blockEquiv]

@[simp] lemma blockEquiv_second {m n m' n' : ℕ}
    (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n') (i : Fin n) :
    blockEquiv e f (Fin.natAdd m i) = Fin.natAdd m' (f i) := by simp [blockEquiv]

/-- 全単射から添字圏の同型へ戻す。 -/
def isoOfEquiv {X Y : FiniteBijection} (e : Fin (card X) ≃ Fin (card Y)) : X ≅ Y where
  hom := homOfEquiv e
  inv := homOfEquiv e.symm
  hom_inv_id := by
    rw [← homOfEquiv_trans (X := X) (Y := Y) (Z := X), Equiv.self_trans_symm]
    exact homOfEquiv_refl X
  inv_hom_id := by
    rw [← homOfEquiv_trans (X := Y) (Y := X) (Z := Y), Equiv.symm_trans_self]
    exact homOfEquiv_refl Y

/-- 直和の結合同型。 -/
def sumAssociator (X Y Z : FiniteBijection) : sumObj (sumObj X Y) Z ≅ sumObj X (sumObj Y Z) :=
  isoOfEquiv (assocEquiv (card X) (card Y) (card Z))

/-- 空集合による左単位同型。 -/
def sumLeftUnitor (X : FiniteBijection) : sumObj (of 0) X ≅ X :=
  isoOfEquiv (finCongr (Nat.zero_add (card X)))

/-- 空集合による右単位同型。 -/
def sumRightUnitor (X : FiniteBijection) : sumObj X (of 0) ≅ X :=
  isoOfEquiv (finCongr (Nat.add_zero (card X)))

/-- 直和の交換同型。 -/
def sumSymmetry (X Y : FiniteBijection) : sumObj X Y ≅ sumObj Y X :=
  isoOfEquiv (swapEquiv (card X) (card Y))

@[simp] lemma equivOfHom_sumMap {X Y X' Y' : FiniteBijection} (f : X ⟶ X') (g : Y ⟶ Y') :
    equivOfHom (sumMap f g) = blockEquiv (equivOfHom f) (equivOfHom g) := by
  exact equivOfHom_homOfEquiv _

@[simp] lemma equivOfHom_sumAssociator (X Y Z : FiniteBijection) :
    equivOfHom (sumAssociator X Y Z).hom = assocEquiv (card X) (card Y) (card Z) :=
  equivOfHom_homOfEquiv _

@[simp] lemma equivOfHom_sumSymmetry (X Y : FiniteBijection) :
    equivOfHom (sumSymmetry X Y).hom = swapEquiv (card X) (card Y) :=
  equivOfHom_homOfEquiv _

/-- 射の等式を標準有限集合の全単射の等式で判定する。 -/
lemma hom_ext {X Y : FiniteBijection} (f g : X ⟶ Y)
    (h : ∀ i, equivOfHom f i = equivOfHom g i) : f = g :=
  (homEquiv X Y).injective (Equiv.ext h)

/-- 結合射の自然性。 -/
lemma sumAssociator_naturality {X Y Z X' Y' Z' : FiniteBijection}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    sumMap (sumMap f g) h ≫ (sumAssociator X' Y' Z').hom =
      (sumAssociator X Y Z).hom ≫ sumMap f (sumMap g h) := by
  apply hom_ext
  intro i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := card X + card Y) (n := card Z)).surjective i
  rcases j with j | j
  · obtain ⟨k, rfl⟩ := (finSumFinEquiv (m := card X) (n := card Y)).surjective j
    cases k <;> simp [Equiv.trans_apply, sumObj]
  · simp [Equiv.trans_apply, sumObj]

/-- 交換射の自然性。 -/
lemma sumSymmetry_naturality {X Y X' Y' : FiniteBijection} (f : X ⟶ X') (g : Y ⟶ Y') :
    sumMap f g ≫ (sumSymmetry X' Y').hom = (sumSymmetry X Y).hom ≫ sumMap g f := by
  apply hom_ext
  intro i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := card X) (n := card Y)).surjective i
  cases j <;> simp [Equiv.trans_apply, sumObj]

@[simp] lemma equivOfHom_sumLeftUnitor (X : FiniteBijection) :
    equivOfHom (sumLeftUnitor X).hom = finCongr (Nat.zero_add (card X)) :=
  equivOfHom_homOfEquiv _

@[simp] lemma equivOfHom_sumRightUnitor (X : FiniteBijection) :
    equivOfHom (sumRightUnitor X).hom = finCongr (Nat.add_zero (card X)) :=
  equivOfHom_homOfEquiv _

/-- 左単位射の自然性。 -/
lemma sumLeftUnitor_naturality {X Y : FiniteBijection} (f : X ⟶ Y) :
    sumMap (𝟙 (of 0)) f ≫ (sumLeftUnitor Y).hom = (sumLeftUnitor X).hom ≫ f := by
  apply hom_ext
  intro i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 0) (n := card X)).surjective i
  rcases j with j | j
  · exact Fin.elim0 j
  · simp only [sumObj, card_of, equivOfHom_comp, equivOfHom_sumMap, equivOfHom_id,
      equivOfHom_sumLeftUnitor, Equiv.trans_apply, finSumFinEquiv_apply_right,
      blockEquiv_second]
    have hc : finCongr (Nat.zero_add (card X)) (Fin.natAdd 0 j) = j := by
      apply Fin.ext
      simp [finCongr]
    rw [hc]
    apply Fin.ext
    simp [finCongr]

/-- 右単位射の自然性。 -/
lemma sumRightUnitor_naturality {X Y : FiniteBijection} (f : X ⟶ Y) :
    sumMap f (𝟙 (of 0)) ≫ (sumRightUnitor Y).hom = (sumRightUnitor X).hom ≫ f := by
  apply hom_ext
  intro i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := card X) (n := 0)).surjective i
  rcases j with j | j
  · simp only [sumObj, card_of, equivOfHom_comp, equivOfHom_sumMap, equivOfHom_id,
      equivOfHom_sumRightUnitor, Equiv.trans_apply, finSumFinEquiv_apply_left,
      blockEquiv_first]
    have hc : finCongr (Nat.add_zero (card X)) (Fin.castAdd 0 j) = j := by
      apply Fin.ext
      simp [finCongr]
    rw [hc]
    apply Fin.ext
    simp [finCongr]
  · exact Fin.elim0 j

/-- 直和の結合射の pentagon。 -/
lemma sumAssociator_pentagon (W X Y Z : FiniteBijection) :
    sumMap (sumAssociator W X Y).hom (𝟙 Z) ≫ (sumAssociator W (sumObj X Y) Z).hom ≫
      sumMap (𝟙 W) (sumAssociator X Y Z).hom =
    (sumAssociator (sumObj W X) Y Z).hom ≫ (sumAssociator W X (sumObj Y Z)).hom := by
  apply hom_ext
  intro i
  obtain ⟨j, rfl⟩ :=
    (finSumFinEquiv (m := (card W + card X) + card Y) (n := card Z)).surjective i
  rcases j with j | j
  · obtain ⟨k, rfl⟩ :=
      (finSumFinEquiv (m := card W + card X) (n := card Y)).surjective j
    rcases k with k | k
    · obtain ⟨l, rfl⟩ := (finSumFinEquiv (m := card W) (n := card X)).surjective k
      cases l <;> simp [Equiv.trans_apply, sumObj]
    · simp [Equiv.trans_apply, sumObj]
  · simp [Equiv.trans_apply, sumObj]

/-- 直和の単位と結合の triangle。 -/
lemma sumAssociator_triangle (X Y : FiniteBijection) :
    (sumAssociator X (of 0) Y).hom ≫ sumMap (𝟙 X) (sumLeftUnitor Y).hom =
      sumMap (sumRightUnitor X).hom (𝟙 Y) := by
  apply hom_ext
  intro i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := card X + 0) (n := card Y)).surjective i
  rcases j with j | j
  · obtain ⟨k, rfl⟩ := (finSumFinEquiv (m := card X) (n := 0)).surjective j
    rcases k with k | k
    · simp only [sumObj, card_of, equivOfHom_comp, equivOfHom_sumMap, equivOfHom_id,
      equivOfHom_sumAssociator, equivOfHom_sumLeftUnitor, equivOfHom_sumRightUnitor,
      Equiv.trans_apply, finSumFinEquiv_apply_left, assocEquiv_first, blockEquiv_first,
      Equiv.refl_apply]
      apply Fin.ext
      simp [finCongr]
    · exact Fin.elim0 k
  · simp only [sumObj, card_of, equivOfHom_comp, equivOfHom_sumMap, equivOfHom_id,
      equivOfHom_sumAssociator, equivOfHom_sumLeftUnitor, equivOfHom_sumRightUnitor,
      Equiv.trans_apply, finSumFinEquiv_apply_right, assocEquiv_third, blockEquiv_second,
      Equiv.refl_apply]
    apply Fin.ext
    simp [finCongr]

/-- 直和の結合と交換の第一の hexagon。 -/
lemma sumAssociator_hexagon_forward (X Y Z : FiniteBijection) :
    (sumAssociator X Y Z).hom ≫ (sumSymmetry X (sumObj Y Z)).hom ≫
      (sumAssociator Y Z X).hom =
    sumMap (sumSymmetry X Y).hom (𝟙 Z) ≫ (sumAssociator Y X Z).hom ≫
      sumMap (𝟙 Y) (sumSymmetry X Z).hom := by
  apply hom_ext
  intro i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := card X + card Y) (n := card Z)).surjective i
  rcases j with j | j
  · obtain ⟨k, rfl⟩ := (finSumFinEquiv (m := card X) (n := card Y)).surjective j
    cases k <;> simp [Equiv.trans_apply, sumObj]
  · simp [Equiv.trans_apply, sumObj]

/-- 二回の交換は恒等射。 -/
lemma sumSymmetry_comp (X Y : FiniteBijection) :
    (sumSymmetry X Y).hom ≫ (sumSymmetry Y X).hom = 𝟙 (sumObj X Y) := by
  apply hom_ext
  intro i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := card X) (n := card Y)).surjective i
  cases j <;> simp [Equiv.trans_apply, sumObj]

@[simp] lemma assocEquiv_symm_first (m n k : ℕ) (i : Fin m) :
    (assocEquiv m n k).symm (Fin.castAdd (n + k) i) = Fin.castAdd k (Fin.castAdd n i) := by
  apply (assocEquiv m n k).injective
  simp

@[simp] lemma assocEquiv_symm_second (m n k : ℕ) (i : Fin n) :
    (assocEquiv m n k).symm (Fin.natAdd m (Fin.castAdd k i)) =
      Fin.castAdd k (Fin.natAdd m i) := by
  apply (assocEquiv m n k).injective
  simp

@[simp] lemma assocEquiv_symm_third (m n k : ℕ) (i : Fin k) :
    (assocEquiv m n k).symm (Fin.natAdd m (Fin.natAdd n i)) = Fin.natAdd (m + n) i := by
  apply (assocEquiv m n k).injective
  simp

@[simp] lemma equivOfHom_sumAssociator_inv (X Y Z : FiniteBijection) :
    equivOfHom (sumAssociator X Y Z).inv = (assocEquiv (card X) (card Y) (card Z)).symm :=
  equivOfHom_homOfEquiv _

/-- 直和の結合と交換の第二の hexagon。 -/
lemma sumAssociator_hexagon_reverse (X Y Z : FiniteBijection) :
    (sumAssociator X Y Z).inv ≫ (sumSymmetry (sumObj X Y) Z).hom ≫
      (sumAssociator Z X Y).inv =
    sumMap (𝟙 X) (sumSymmetry Y Z).hom ≫ (sumAssociator X Z Y).inv ≫
      sumMap (sumSymmetry X Z).hom (𝟙 Y) := by
  apply hom_ext
  intro i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := card X) (n := card Y + card Z)).surjective i
  rcases j with j | j
  · simp [Equiv.trans_apply, sumObj]
  · obtain ⟨k, rfl⟩ := (finSumFinEquiv (m := card Y) (n := card Z)).surjective j
    cases k <;> simp [Equiv.trans_apply, sumObj]

end SerrePositivity.FiniteBijection
