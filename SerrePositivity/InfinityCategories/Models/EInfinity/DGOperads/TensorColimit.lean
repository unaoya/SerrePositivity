module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamily
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits

/-!
模型。文献の定義との比較は後で
# 独立な有限個の図式のテンソルと余極限

概要：Berger–Moerdijk §1 の自由代数の構成に用いる、テンソル冪の余極限表示を構成する。
方針：独立な添字の直積を再帰で作り、Mathlib の二変数の余極限保存を適用する。
規約：空の直積は一点圏、空のテンソルは単位複体。
使われ方：Schur 生成射上の等変な演算を Schur 入力のテンソル冪からの射へ降ろす。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

/-- 概要：独立な n 個の添字の直積（Berger–Moerdijk §1）。
方針：先頭の添字と残りの直積で再帰する。
規約：空の直積を一点離散圏の対象型とする。
使われ方：Schur 図式の n 個の独立なコピーを添字付ける。 -/
def tensorIndex (J : Type) : ℕ → Type
  | 0 => Discrete PUnit
  | n + 1 => J × tensorIndex J n

/-- 概要：独立な添字の直積圏（Berger–Moerdijk §1）。
方針：一点離散圏と既存の直積圏の構造を使う。
規約：添字圏は小さい。
使われ方：有限テンソルの図式の源圏となる。 -/
instance tensorIndexCategory (J : Type) [SmallCategory J] : ∀ n, SmallCategory (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex J n)
  | 0 => inferInstanceAs (SmallCategory (Discrete PUnit))
  | n + 1 => by
    let := tensorIndexCategory J n
    exact inferInstanceAs (SmallCategory (J × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex J n))

/-- 概要：独立な添字の直積を有限族として読む（Berger–Moerdijk §1）。
方針：先頭の添字を追加する再帰を使う。
規約：空の族には `Fin.elim0` を用いる。
使われ方：余極限の添字と全入力への合成の arity 族を接続する。 -/
def tensorIndexFamily (J : Type) : ∀ n, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex J n → (Fin n → J)
  | 0, _ => Fin.elim0
  | n + 1, j => Fin.cons (α := fun _ : Fin (n + 1) => J) j.1 (tensorIndexFamily J n j.2)

/-- 概要：有限族を独立な添字の直積へ戻す（Berger–Moerdijk §1）。
方針：族の先頭と残りの族に分ける再帰を使う。
規約：空の族は一点圏の唯一の対象へ送る。
使われ方：arity 族を余極限の具体的な生成射の添字へ送る。 -/
def tensorIndexOfFamily (J : Type) : ∀ n, (Fin n → J) → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex J n
  | 0, _ => ⟨PUnit.unit⟩
  | n + 1, s => (s 0, tensorIndexOfFamily J n (fun i => s i.succ))

/-- 概要：独立な添字と有限族の間の同値（Berger–Moerdijk §1）。
方針：先頭と残りに関する二つの再帰が互いに逆であることを示す。
規約：対象の型の同値であり、ここでは添字圏の構造を移さない。
使われ方：余極限の全ての生成射を arity の有限族で調べる。 -/
def tensorIndexEquivFamily (J : Type) (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex J n ≃ (Fin n → J) where
  toFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily J n
  invFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexOfFamily J n
  left_inv j := by
    induction n with
    | zero => rcases j with ⟨⟨⟩⟩; rfl
    | succ n ih =>
      rcases j with ⟨a, j⟩
      change (a, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexOfFamily J n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily J n j)) = (a, j)
      rw [ih j]
  right_inv s := by
    induction n with
    | zero => funext i; exact Fin.elim0 i
    | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact congrFun (ih (fun i => s i.succ)) i

/-- 概要：有限族を添字の直積へ送り戻すと元の族になる（Berger–Moerdijk §1）。
方針：直積と有限族の同値の逆律を適用する。
規約：任意の対象型の有限族を扱う。
使われ方：arity 族で指定した生成射を余極限の添字へ移す。 -/
@[simp]
lemma tensorIndexFamily_ofFamily (J : Type) (n : ℕ) (s : Fin n → J) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily J n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexOfFamily J n s) = s :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexEquivFamily J n).apply_symm_apply s

variable {A : Type u} [CommRing A] {J : Type} [SmallCategory J]

/-- 概要：図式の n 個の独立なコピーの外部テンソル積（Berger–Moerdijk §1）。
方針：既存の externalProduct を再帰的に用いる。
規約：空の外部テンソル積は単位複体の定値図式。
使われ方：Schur 入力のテンソル冪を余極限で表す。 -/
def tensorIndexDiagram (F : J ⥤ Complex A) : ∀ n, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex J n ⥤ Complex A
  | 0 => (Functor.const _).obj (𝟙_ (Complex A))
  | n + 1 => externalProduct F (tensorIndexDiagram F n)

/-- 概要：外部テンソル図式の対象は有限テンソル族に一致する（Berger–Moerdijk §1）。
方針：図式と有限族の再帰を比較する。
規約：各入力をその添字における元の図式の値に送る。
使われ方：全入力への合成の生成射を外部テンソル図式の対象で記述する。 -/
lemma tensorIndexDiagram_obj (F : J ⥤ Complex A) (n : ℕ) (j : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex J n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram F n).obj j =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => F.obj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily J n j i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases j with ⟨a, j⟩
    change F.obj a ⊗ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram F n).obj j =
      F.obj a ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => F.obj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily J n j i))
    rw [ih j]

/-- 概要：元の余錐の構造射を独立な入力ごとにテンソルする（Berger–Moerdijk §1）。
方針：各入力の構造射を再帰的にテンソルし、その自然性を使う。
規約：標的は既存の右括弧テンソル冪の定値図式。
使われ方：余極限の頂点を型の上でもテンソル冪に固定する。 -/
def tensorIndexLeg {F : J ⥤ Complex A} (c : Cocone F) :
    ∀ n, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram F n ⟶ (Functor.const _).obj (_root_.SerrePositivity.TensorPowers.power c.pt n)
  | 0 => 𝟙 _
  | n + 1 => {
    app j := c.ι.app j.1 ⊗ₘ (tensorIndexLeg c n).app j.2
    naturality := fun {j k} f => by
      change ((F.map f.1 ▷ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram F n).obj j.2) ≫
        (F.obj k.1 ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram F n).map f.2)) ≫
        (c.ι.app k.1 ⊗ₘ (tensorIndexLeg c n).app k.2) =
          (c.ι.app j.1 ⊗ₘ (tensorIndexLeg c n).app j.2) ≫ 𝟙 _
      rw [← tensorHom_def, Category.comp_id, tensorHom_comp_tensorHom, c.w f.1]
      have h := (tensorIndexLeg c n).naturality f.2
      change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram F n).map f.2 ≫ (tensorIndexLeg c n).app k.2 =
        (tensorIndexLeg c n).app j.2 ≫ 𝟙 _ at h
      rw [Category.comp_id] at h
      rw [h] }

/-- 概要：元の余錐の n 個のコピーのテンソル余錐（Berger–Moerdijk §1）。
方針：構造射の有限テンソルを余錐に束ねる。
規約：頂点を既存のテンソル冪に固定して定義する。
使われ方：Schur 生成射のテンソルを余極限の構造射として実現する。 -/
def tensorIndexCocone {F : J ⥤ Complex A} (c : Cocone F) (n : ℕ) :
    Cocone (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram F n) where
  pt := _root_.SerrePositivity.TensorPowers.power c.pt n
  ι := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexLeg c n

/-- 概要：テンソル余錐の構造射は入力ごとの生成射の有限テンソルに等しい（Berger–Moerdijk §1）。
方針：図式の対象と有限テンソル族を比較し、長さの帰納法で構造射を同定する。
規約：対象の比較に必要な等式による移送を明示する。
使われ方：Schur 作用の生成射上の式と余極限による降下を接続する。 -/
lemma tensorIndexLeg_eq_generator {F : J ⥤ Complex A} (c : Cocone F) (n : ℕ)
    (j : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex J n) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram_obj F n j) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator c.pt F.obj (fun i => c.ι.app i) n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily J n j) =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexLeg c n).app j := by
  induction n with
  | zero => exact Category.id_comp _
  | succ n ih =>
    rcases j with ⟨a, j⟩
    have he : eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram_obj F (n + 1) (a, j)) =
        F.obj a ◁ eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram_obj F n j) := by
      rw [whiskerLeft_eqToHom]
    change eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram_obj F (n + 1) (a, j)) ≫
      (c.ι.app a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator c.pt F.obj (fun i => c.ι.app i) n
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily J n j)) = c.ι.app a ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexLeg c n).app j
    rw [he, whiskerLeft_comp_tensorHom, ih j]

/-- 概要：元の余錐が余極限なら独立なコピーのテンソル余錐も余極限（Berger–Moerdijk §1）。
方針：閉モノイダル構造の各変数の余極限保存と Mathlib の二変数の保存定理を使う。
規約：添字は直積であり、同一添字への対角制限を取らない。
使われ方：各入力の coinvariant 関係を保つ演算を Schur 入力のテンソル冪へ降ろす。 -/
def tensorIndexCoconeIsColimit {F : J ⥤ Complex A} {c : Cocone F} (hc : IsColimit c) :
    ∀ n, IsColimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexCocone c n)
  | 0 => {
    desc t := t.ι.app ⟨PUnit.unit⟩
    fac t j := by
      rcases j with ⟨⟨⟩⟩
      exact Category.id_comp _
    uniq t m hm := by
      have h := hm ⟨PUnit.unit⟩
      change 𝟙 _ ≫ m = t.ι.app ⟨PUnit.unit⟩ at h
      simpa only [Category.id_comp] using h }
  | n + 1 =>
    IsColimit.ofIsoColimit (hc.tensor₂ (tensorIndexCoconeIsColimit hc n))
      (Cocone.ext (Iso.refl _) (fun j => by
        change ((c.ι.app j.1 ▷ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram F n).obj j.2) ≫
          (c.pt ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexLeg c n).app j.2)) ≫ 𝟙 _ =
            c.ι.app j.1 ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexLeg c n).app j.2
        rw [Category.comp_id]
        exact (tensorHom_def (c.ι.app j.1) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexLeg c n).app j.2)).symm))

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
