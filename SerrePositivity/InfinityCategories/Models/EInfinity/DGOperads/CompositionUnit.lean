module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedCompositionEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionUnit

/-!
模型。文献の定義との比較は後で
# 全入力への合成の一次の場合と単位則

概要：Berger–Moerdijk §1 の単位演算による代入を、構成した全入力への合成で計算する。
方針：一次の場合を通常の部分合成へ簡約し、オペラッドの左単位則を適用する。
規約：内側 arity は 0 を含む任意の自然数とする。
使われ方：Schur 対象上の作用射が単位演算を恒等射として作用させることを証明する。
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

/-- 概要：全入力への合成の一次の場合は通常の部分合成に一致する（Berger–Moerdijk §1）。
方針：空の残りの演算族を右単位子で除き、arity の移送を最後にまとめる。
規約：内側の arity の有限族は一要素。
使われ方：自由代数の単位作用の生成射上の式を簡約する。 -/
lemma composition_one (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (s : Fin 1 → ℕ) :
    P.composition 1 s =
      (P.arity 1 ◁ (ρ_ (P.arity (s 0))).hom) ≫ P.comp 0 (s 0) 0 ≫
        eqToHom (congrArg P.arity (by simp : 0 + s 0 = ∑ i, s i)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composition
  rw [P.composeFirstInputs_succ_factor]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs, eqToHom_refl, id_whiskerRight, Category.id_comp, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep_zero_post]
  simp only [Category.assoc, eqToHom_trans, Category.comp_id]
  rfl

/-- 概要：全入力への一次の合成で外側が単位演算なら内側演算を返す（Berger–Moerdijk §1）。
方針：一次の合成を部分合成へ簡約し、オペラッドの左単位則を適用する。
規約：内側の一要素の有限テンソルの最後の単位は右単位子で除く。
使われ方：Schur 作用の単位則を生成射上で証明する。 -/
lemma unit_composition_one (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (s : Fin 1 → ℕ) :
    (P.unit ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily 1 (fun i => P.arity (s i))) ≫ P.composition 1 s =
      (λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily 1 (fun i => P.arity (s i)))).hom ≫
        (ρ_ (P.arity (s 0))).hom ≫
          eqToHom (congrArg P.arity (by simp : s 0 = ∑ i, s i)) := by
  have hc : (P.unit ▷ P.arity (s 0)) ≫ P.comp 0 (s 0) 0 ≫
      eqToHom (congrArg P.arity (by simp : 0 + s 0 = ∑ i, s i)) =
    (λ_ (P.arity (s 0))).hom ≫
      eqToHom (congrArg P.arity (by simp : s 0 = ∑ i, s i)) := by
    have h := congrArg (· ≫ eqToHom (congrArg P.arity (by simp : s 0 = ∑ i, s i)))
      (P.unit_comp (s 0))
    simp only [Category.assoc, eqToHom_trans] at h
    exact h
  rw [P.composition_one, ← whisker_exchange_assoc, hc, leftUnitor_naturality_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
