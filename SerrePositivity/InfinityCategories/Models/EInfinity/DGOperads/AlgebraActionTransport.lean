module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedCompositionEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionCore

/-!
模型。文献の定義との比較は後で
# 代数の作用と反復合成の添字の移送

概要：Berger–Moerdijk §1 の代数の部分合成則を、反復代入の添字で表す。
方針：係数と入力の同時の移送を相殺し、部分合成則の入出力の長さを明示する。
規約：代入する演算の arity と末尾の入力数は零を許す。
使われ方：自由代数からの評価射の作用保存を、反復合成に沿って証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：代数の作用は係数と入力の同時の arity の移送を相殺する（Berger–Moerdijk §1）。
方針：長さの等式を消去して恒等射を除く。
規約：任意の P 代数に適用する。
使われ方：全合成の総 arity の表示を代数の作用の手前で揃える。 -/
@[reassoc]
lemma action_index_eq (X : P.Algebra) {m n : ℕ} (h : m = n) :
    (eqToHom (congrArg P.arity h) ⊗ₘ eqToHom (congrArg (power X.carrier) h)) ≫
      X.action n = X.action m := by
  subst n
  simp only [eqToHom_refl, tensorHom_id, id_whiskerRight, Category.id_comp]

/-- 概要：部分合成則の外側と出力の arity を任意の等しい表示へ移せる（Berger–Moerdijk §1）。
方針：二つの長さの等式を消去して代数の部分合成公理を用いる。
規約：移送後の入力の順序は変えない。
使われ方：反復代入の一段を部分合成の評価へ帰着する。 -/
lemma comp_action_transport (X : P.Algebra) (m n : ℕ) (i : Fin (m + 1))
    {r t : ℕ} (hr : r = m + 1) (ht : m + n = t) :
    (((eqToHom (congrArg P.arity hr) ▷ P.arity n) ≫ P.comp m n i ≫
      eqToHom (congrArg P.arity ht)) ▷ power X.carrier t) ≫ X.action t =
    (α_ (P.arity r) (P.arity n) (power X.carrier t)).hom ≫
      (P.arity r ◁ ((P.arity n ◁ eqToHom (congrArg (power X.carrier) ht.symm)) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X.carrier (P.arity n) m n i (X.action n) ≫
        eqToHom (congrArg (power X.carrier) hr.symm))) ≫ X.action r := by
  subst r
  subst t
  simpa only [eqToHom_refl, id_whiskerRight, Category.id_comp, Category.comp_id,
    whiskerLeft_id] using X.comp_action m n i

/-- 概要：反復代入の最後の指定入力への合成を代数で評価する（Berger–Moerdijk §1）。
方針：位置 n の部分合成則を用い、前方 n と後方 k の入力を明示する。
規約：新しい尾の長さは k+l と書き、入力の実際の順序は l 個、k 個を保つ。
使われ方：先頭入力への反復代入の帰納段階で合成演算を作用の合成へ変える。 -/
lemma composeFirstInputInsertion_action (X : P.Algebra) (n k l : ℕ) :
    (P.composeFirstInputInsertion n k l ▷ power X.carrier (n + (k + l))) ≫
      X.action (n + (k + l)) =
    (α_ (P.arity (n + 1 + k)) (P.arity l) (power X.carrier (n + (k + l)))).hom ≫
      (P.arity (n + 1 + k) ◁
        ((P.arity l ◁ eqToHom (congrArg (power X.carrier)
          (by omega : n + (k + l) = n + (l + k)))) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionCore X.carrier (P.arity l) n l k (X.action l) ≫
        eqToHom (congrArg (power X.carrier)
          (by omega : n + (k + 1) = n + 1 + k)))) ≫ X.action (n + 1 + k) := by
  have h := X.comp_action_transport (n + k) l ⟨n, by omega⟩
    (by omega : n + 1 + k = n + k + 1) (Nat.add_assoc n k l)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_at_sum] at h
  simp only [whiskerLeft_comp, Category.assoc] at h
  simp only [← whiskerLeft_comp_assoc, eqToHom_trans] at h
  exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
