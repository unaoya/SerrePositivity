module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TwoSlotPermutations
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedCompositionEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ArityBijectionTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionSwap

/-!
模型。文献の定義との比較は後で
# 任意の異なる二入力への代入の交換

概要：Berger–Moerdijk §1 の異なる二入力への代入と外側の入力交換の両立を証明する。
方針：右の入力を先に代入する射を定義し、部分合成の交換則と外側等変性を二回使う。
規約：外側 arity は m+2、二つの代入位置は i<j、残りの入力は保持する。
使われ方：全入力への反復合成の外側等変性で隣接する二つの代入を交換する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：異なる二入力へ右から順に代入する合成射（Berger–Moerdijk §1）。
方針：右の演算を係数の隣へ移して部分合成し、左の入力にも代入する。
規約：m 個の他の入力を残し、終域の arity を m+a+b とする。
使われ方：任意の外側 arity の二つの代入を一つの射として扱う。 -/
def twoSlotComposition (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m a b : ℕ) (i j : Fin (m + 2))
    (_hij : i.val < j.val) :
    P.arity (m + 2) ⊗ (P.arity a ⊗ P.arity b) ⟶ P.arity ((m + a) + b) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.comp (m + 1) b j)
    ((eqToHom (congrArg P.arity (by omega : (m + 1) + b = (m + b) + 1)) ▷ P.arity a) ≫
      P.comp (m + b) a ⟨i.val, by omega⟩ ≫
        eqToHom (congrArg P.arity (by omega : (m + b) + a = (m + a) + b)))

/-- 概要：二入力への代入は左から先に代入する式に一致する（Berger–Moerdijk §1）。
方針：部分合成の交換則を適用し、テンソル対象の等式の射を whisker へ移す。
規約：左への代入後の右の位置は j+a-1 である。
使われ方：外側の互換を二回の部分合成に適用した式を元の合成と比較する。 -/
lemma twoSlotComposition_parallel (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m a b : ℕ) (i j : Fin (m + 2))
    (hij : i.val < j.val) :
    (α_ (P.arity (m + 2)) (P.arity a) (P.arity b)).hom ≫
        P.twoSlotComposition m a b i j hij =
      (P.comp (m + 1) a i ▷ P.arity b) ≫
        (eqToHom (congrArg P.arity (by omega : (m + 1) + a = (m + a) + 1)) ▷ P.arity b) ≫
        P.comp (m + a) b ⟨j.val + a - 1, by omega⟩ := by
  have h := P.parallel_assoc m a b i j hij
  have ha : eqToHom (congrArg (fun q => P.arity q ⊗ P.arity b)
      (by omega : (m + 1) + a = (m + a) + 1)) =
    eqToHom (congrArg P.arity (by omega : (m + 1) + a = (m + a) + 1)) ▷ P.arity b := by
    rw [eqToHom_whiskerRight]
  have hb : eqToHom (congrArg (fun q => P.arity q ⊗ P.arity a)
      (by omega : (m + 1) + b = (m + b) + 1)) =
    eqToHom (congrArg P.arity (by omega : (m + 1) + b = (m + b) + 1)) ▷ P.arity a := by
    rw [eqToHom_whiskerRight]
  rw [ha, hb] at h
  exact h.symm

/-- 概要：任意の二入力への代入はその入力の互換に関して等変である（Berger–Moerdijk §1）。
方針：二つの部分合成の外側等変性、代入位置の計算、異なる入力への代入の交換則を使う。
規約：内側二因子の交換は Koszul 対称性を含み、他の外側入力を保持する。
使われ方：全入力への合成の外側等変性を隣接する二つの代入について証明する。 -/
lemma twoSlotComposition_outer_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m a b : ℕ)
    (i j : Fin (m + 2)) (hij : i.val < j.val) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (m + 2) (Equiv.swap i j)) ⊗ₘ
        (β_ (P.arity a) (P.arity b)).hom) ≫ P.twoSlotComposition m b a i j hij =
      P.twoSlotComposition m a b i j hij ≫ P.sequence.map
        (_root_.SerrePositivity.FiniteBijection.homOfEquiv (X := _root_.SerrePositivity.FiniteBijection.of ((m + a) + b))
          (Y := _root_.SerrePositivity.FiniteBijection.of ((m + b) + a)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotOutputEquiv m a b i j hij)) := by
  let C := P.arity (m + 2)
  let U := P.arity a
  let V := P.arity b
  let A₀ := P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (m + 2) (Equiv.swap i j))
  let t := P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((m + 1) + a)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (m + 1) a i (Equiv.swap i j)))
  let t' := P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((m + a) + 1)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotAfterFirst m a i j))
  let w := P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((m + a) + b)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (m + a) b ⟨j.val + a - 1, by omega⟩
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotAfterFirst m a i j)))
  let c := eqToHom (congrArg P.arity (by omega : (m + 1) + a = (m + a) + 1))
  let v := eqToHom (congrArg P.arity (by omega : (m + a) + b = (m + b) + a))
  let f₀ := P.comp (m + 1) a i
  let f₁ := P.comp (m + 1) a j
  let g₀ := P.comp (m + a) b ⟨i.val, by omega⟩
  let g₁ := P.comp (m + a) b ⟨j.val + a - 1, by omega⟩
  let B := P.sequence.map (_root_.SerrePositivity.FiniteBijection.homOfEquiv (X := _root_.SerrePositivity.FiniteBijection.of ((m + a) + b))
    (Y := _root_.SerrePositivity.FiniteBijection.of ((m + b) + a)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotOutputEquiv m a b i j hij))
  have hfirst : (A₀ ▷ U) ≫ f₁ = f₀ ≫ t := by
    have h := P.outer_equivariance (m + 1) a i (Equiv.swap i j)
    rw [Equiv.swap_apply_left] at h
    exact h
  have hmove : (t ▷ V) ≫ (c ▷ V) = (c ▷ V) ≫ (t' ▷ V) := by
    have h := congrArg (· ▷ V) (P.arity_permutation_index_eq
      (by omega : (m + 1) + a = (m + a) + 1)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (m + 1) a i (Equiv.swap i j))).symm
    simp only [comp_whiskerRight] at h
    exact h
  have hsecond : (t' ▷ V) ≫ g₀ = g₁ ≫ w := by
    have h := P.outer_equivariance (m + a) b ⟨j.val + a - 1, by omega⟩
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotAfterFirst m a i j)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotAfterFirst_remaining m a i j hij] at h
    exact h
  have houtput : w ≫ v = B := by
    let σ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (m + a) b ⟨j.val + a - 1, by omega⟩
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotAfterFirst m a i j)
    have h := P.arity_map_permutation_transport (rfl : (m + a) + b = (m + a) + b)
      (by omega : (m + a) + b = (m + b) + a) σ
    have he : ((finCongr (rfl : (m + a) + b = (m + a) + b)).symm.trans
        (σ.trans (finCongr (by omega : (m + a) + b = (m + b) + a)))) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTwoSlotOutputEquiv m a b i j hij := by
      apply Equiv.ext
      intro x
      rfl
    rw [he] at h
    simpa only [eqToHom_refl, Category.id_comp] using h
  have hparallel : P.twoSlotComposition m a b i j hij =
      (α_ C U V).inv ≫ (f₀ ▷ V) ≫ (c ▷ V) ≫ g₁ := by
    have h := congrArg ((α_ C U V).inv ≫ ·) (P.twoSlotComposition_parallel m a b i j hij)
    dsimp only [C, U, V] at h
    rw [Iso.inv_hom_id_assoc] at h
    exact h
  have hf : (((A₀ ▷ U) ≫ f₁) ▷ V) = (f₀ ▷ V) ≫ (t ▷ V) :=
    (congrArg (· ▷ V) hfirst).trans (comp_whiskerRight f₀ t V)
  have hm := congrArg (· ≫ g₀ ≫ v) hmove
  simp only [Category.assoc] at hm
  have hs := congrArg (· ≫ v) hsecond
  simp only [Category.assoc] at hs
  calc
    _ = (α_ C U V).inv ≫ (((A₀ ▷ U) ≫ f₁) ▷ V) ≫ (c ▷ V) ≫ g₀ ≫ v :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_swap A₀ f₁ ((c ▷ V) ≫ g₀ ≫ v)
    _ = (α_ C U V).inv ≫ (f₀ ▷ V) ≫ (t ▷ V) ≫ (c ▷ V) ≫ g₀ ≫ v := by
      rw [hf, Category.assoc]
    _ = (α_ C U V).inv ≫ (f₀ ▷ V) ≫ (c ▷ V) ≫ (t' ▷ V) ≫ g₀ ≫ v := by rw [hm]
    _ = (α_ C U V).inv ≫ (f₀ ▷ V) ≫ (c ▷ V) ≫ g₁ ≫ B := by rw [hs, houtput]
    _ = _ := by simpa only [Category.assoc] using (congrArg (· ≫ B) hparallel).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
