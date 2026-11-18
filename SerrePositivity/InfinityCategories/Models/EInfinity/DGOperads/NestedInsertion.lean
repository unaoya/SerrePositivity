module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FirstInputComposite
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedCompositionEquivariance

/-!
模型。文献の定義との比較は後で
# 外側合成と一段の入れ子の挿入

概要：Berger–Moerdijk §1 の nested_assoc を反復合成の一段の挿入に適用する。
方針：始域の arity の移送を相殺し、部分合成の添字と出力を移送する。
規約：外側の代入位置は 0、内側の指定入力の最後は n 番目。
使われ方：反復合成と先頭入力への部分合成の結合則の帰納段階を与える。
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

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：一段の挿入の始域を標準の部分合成の arity に移す（Berger–Moerdijk §1）。
方針：挿入の定義の最初の arity の移送を相殺する。
規約：代入位置 n と内側 arity l を固定する。
使われ方：入れ子の挿入の内側を nested_assoc の部分合成へ直す。 -/
lemma composeFirstInputInsertion_raw (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k l : ℕ) :
    (eqToHom (congrArg P.arity (by omega : n + k + 1 = n + 1 + k)) ▷ P.arity l) ≫
      P.composeFirstInputInsertion n k l =
    P.comp (n + k) l ⟨n, by omega⟩ ≫
      eqToHom (congrArg P.arity (Nat.add_assoc n k l)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputInsertion
  rw [← comp_whiskerRight_assoc, eqToHom_trans]
  simp only [eqToHom_refl, id_whiskerRight, Category.id_comp]

/-- 概要：外側合成後の挿入を nested_assoc の外側 arity で計算する（Berger–Moerdijk §1）。
方針：挿入の最初の移送をまとめ、部分合成の外側の添字の移送を適用する。
規約：交換する位置の値 n は変えない。
使われ方：反復合成の帰納段階の二回目の部分合成をそろえる。 -/
lemma composeFirstInputInsertion_outer_cast (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n k l : ℕ) :
    (eqToHom (congrArg P.arity
      (by omega : m + (n + k + 1) = n + 1 + (m + k))) ▷ P.arity l) ≫
      P.composeFirstInputInsertion n (m + k) l ≫
        eqToHom (congrArg P.arity
          (by omega : n + ((m + k) + l) = n + (m + (k + l)))) =
    P.comp (m + (n + k)) l ⟨n, by omega⟩ ≫
      eqToHom (congrArg P.arity
        (by omega : (m + (n + k)) + l = n + (m + (k + l)))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputInsertion
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, eqToHom_trans]
  have h := P.comp_slot_output_cast (by omega : m + (n + k) = n + (m + k)) l
    (⟨n, by omega⟩ : Fin (m + (n + k) + 1))
  have hp := congrArg (· ≫ eqToHom (congrArg P.arity
    (by omega : n + (m + k) + l = n + (m + (k + l))))) h
  simp only [Category.assoc, eqToHom_trans] at hp
  simp only [eqToHom_trans]
  exact hp

/-- 概要：先頭入力への外側合成と内側の最後の指定入力への挿入は結合的である（Berger–Moerdijk §1）。
方針：内側 arity の移送で前合成して相殺し、nested_assoc と挿入の移送の式を使う。
規約：出力は n+(m+(k+l)) の表記で統一する。
使われ方：入れ子の反復合成の結合則の帰納段階の最初の正方形となる。 -/
lemma composeIntoFirst_insertion (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n k l : ℕ) :
    (P.composeIntoFirst m (n + 1) k ▷ P.arity l) ≫
      P.composeFirstInputInsertion n (m + k) l ≫
        eqToHom (congrArg P.arity
          (by omega : n + ((m + k) + l) = n + (m + (k + l)))) =
    (α_ (P.arity (m + 1)) (P.arity (n + 1 + k)) (P.arity l)).hom ≫
      (P.arity (m + 1) ◁ P.composeFirstInputInsertion n k l) ≫
        P.composeIntoFirst m n (k + l) := by
  let hr : n + k + 1 = n + 1 + k := by omega
  apply (cancel_epi ((P.arity (m + 1) ◁ eqToHom (congrArg P.arity hr)) ▷ P.arity l)).1
  rw [← comp_whiskerRight_assoc,
    P.composeIntoFirst_input_cast m (n + 1) k hr, comp_whiskerRight_assoc]
  rw [P.composeFirstInputInsertion_outer_cast m n k l]
  rw [associator_naturality_middle_assoc]
  rw [← whiskerLeft_comp_assoc, P.composeFirstInputInsertion_raw n k l]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [P.composeIntoFirst_input_cast m n (k + l) (Nat.add_assoc n k l)]
  have h := congrArg (· ≫ eqToHom (congrArg P.arity
    (by omega : (m + (n + k)) + l = n + (m + (k + l)))))
      (P.nested_assoc m (n + k) l (0 : Fin (m + 1)) ⟨n, by omega⟩)
  simp only [Category.assoc, eqToHom_trans] at h
  simpa only [Fin.val_zero, Nat.zero_add] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
