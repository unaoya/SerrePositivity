module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionBinary
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionMiddle

/-!
模型。文献の定義との比較は後で
# 二入力への部分合成の交換

概要：Berger–Moerdijk §1 の異なる入力への代入の交換則を、二入力の合成射として記述する。
方針：二番目の入力を先に代入する射を定義し、部分合成の交換則で逆順の式と比較する。
規約：arity の加法の移送は等式の射を用い、係数の交換は Koszul 対称性を用いる。
使われ方：全入力への合成の外側等変性の隣接交換の場合に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]


/-- 概要：二番目の入力を先に代入する二入力の合成射（Berger–Moerdijk §1）。
方針：内側の係数を交換し、二番目の部分合成の後に先頭への部分合成を適用する。
規約：終域は入力の元の順序に対応する arity a+b。
使われ方：二入力の全合成の計算と外側等変性の基底に用いる。 -/
def binaryComposition (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (a b : ℕ) :
    P.arity 2 ⊗ (P.arity a ⊗ P.arity b) ⟶ P.arity (a + b) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.comp 1 b 1)
    ((eqToHom (congrArg P.arity (by omega : 1 + b = (0 + b) + 1)) ▷ P.arity a) ≫
      P.comp (0 + b) a 0 ≫
        eqToHom (congrArg P.arity (by omega : (0 + b) + a = a + b)))

/-- 概要：二入力の合成は先頭の入力を先に代入する式に一致する（Berger–Moerdijk §1）。
方針：部分合成の異なる入力への交換則に出力 arity の移送を合成する。
規約：係数の二つの arity は 0 を含む。
使われ方：隣接入力を交換した全合成を同じ順序の式にそろえる。 -/
lemma binaryComposition_parallel (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (a b : ℕ) :
    (α_ (P.arity 2) (P.arity a) (P.arity b)).hom ≫ P.binaryComposition a b =
      (P.comp 1 a 0 ▷ P.arity b) ≫
        (eqToHom (congrArg P.arity (by omega : 1 + a = (0 + a) + 1)) ▷ P.arity b) ≫
          P.comp (0 + a) b ⟨a, by omega⟩ ≫
            eqToHom (congrArg P.arity (by omega : (0 + a) + b = a + b)) := by
  have h := congrArg (· ≫ eqToHom (congrArg P.arity (by omega : (0 + a) + b = a + b)))
    (P.parallel_assoc 0 a b 0 1 (by decide))
  have hi : (⟨(1 : Fin 2).val + a - 1, by omega⟩ : Fin ((0 + a) + 1)) = ⟨a, by omega⟩ := by
    apply Fin.ext
    change 1 + a - 1 = a
    omega
  have ha : eqToHom (congrArg (fun q => P.arity q ⊗ P.arity b)
      (by omega : 1 + a = (0 + a) + 1)) =
    eqToHom (congrArg P.arity (by omega : 1 + a = (0 + a) + 1)) ▷ P.arity b := by
    rw [eqToHom_whiskerRight]
  have hb : eqToHom (congrArg (fun q => P.arity q ⊗ P.arity a)
      (by omega : 1 + b = (0 + b) + 1)) =
    eqToHom (congrArg P.arity (by omega : 1 + b = (0 + b) + 1)) ▷ P.arity a := by
    rw [eqToHom_whiskerRight]
  rw [hi, ha, hb] at h
  simp only [Category.assoc, eqToHom_trans] at h
  exact h.symm

set_option maxHeartbeats 1000000 in
-- 二入力の再帰の arity の移送と単位子を同時に正規化するため、この宣言だけ上限を増やす。
/-- 概要：二入力の全合成はテンソル単位を除いた二入力の部分合成に一致する（Berger–Moerdijk §1）。
方針：最後の入力からの再帰を展開し、残り一入力の式と代入の自然性を適用する。
規約：終域の arity の有限和への移送を最後に置く。
使われ方：全入力への合成の外側等変性の二入力の場合を部分合成の交換則へ帰着する。 -/
lemma composition_two (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (s : Fin 2 → ℕ) :
    P.composition 2 s =
      (P.arity 2 ◁ (P.arity (s 0) ◁ (ρ_ (P.arity (s 1))).hom)) ≫
        P.binaryComposition (s 0) (s 1) ≫
          eqToHom (congrArg P.arity (by simp [Fin.sum_univ_succ] : s 0 + s 1 = ∑ i, s i)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composition
  simp only [eqToHom_refl, id_whiskerRight, Category.id_comp, Category.comp_id]
  rw [P.composeFirstInputs_succ_factor]
  simp only [eqToHom_refl, id_whiskerRight, Category.id_comp]
  rw [P.composeFirstInputs_one]
  simp only [Category.assoc, eqToHom_trans]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep_first_post]
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, eqToHom_trans]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep_one (fun i => P.arity (s i))
    (P.comp 1 (s 1) 1)
    ((eqToHom (congrArg P.arity (by omega : 1 + s 1 = (0 + s 1) + 1)) ▷ P.arity (s 0)) ≫
      P.comp (0 + s 1) (s 0) 0 ≫
        eqToHom (congrArg P.arity (by omega : (0 + s 1) + s 0 = s 0 + s 1)))

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
