module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.Order.Fin.Basic

/-!
概要：有限実鎖の面を実順序関手で構成し、尾部・先頭の挿入との合成則を照合する。
方針：一点を飛ばす実順序埋め込みと既存のprecompを使う。
規約：対象だけでなく全関手の面の等式を証明する。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の指定面、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実細分と面の照合。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：指定した一点を飛ばす実有限順序関手。
方針：有限順序埋め込みから作る。規約：全射の作用を保持する。
使われ方：Riehl–Verity §4.1の指定面。 -/
def finiteChainFaceIndex {n : ℕ} (k : Fin (n + 2)) : Fin (n + 1) ⥤ Fin (n + 2) :=
  (Fin.succAboveOrderEmb k).monotone.functor

/-- 概要：一点を飛ばす関手と尾部への包含の全合成則。
方針：後続点でのsuccAboveの法則と薄い順序圏の射の一意性を使う。
規約：全関手の等式。使われ方：Riehl–Verity §4.1の細分の尾部の面。 -/
lemma finiteChainFaceIndex_succ {n : ℕ} (k : Fin (n + 2)) :
    Fin.succFunctor (n + 1) ⋙ finiteChainFaceIndex k.succ =
      finiteChainFaceIndex k ⋙ Fin.succFunctor (n + 2) := by
  refine CategoryTheory.Functor.ext (fun i => Fin.succ_succAbove_succ k i) ?_
  intro i j f
  exact Subsingleton.elim _ _

variable {C : Type u} [Category.{v} C]

/-- 概要：元の実有限鎖の指定した面。
方針：一点を飛ばす実順序関手で前合成する。規約：元の実関手を使う。
使われ方：Riehl–Verity §4.1の親の面の検収。 -/
def finiteChainFace {n : ℕ} (F : ComposableArrows C (n + 1)) (k : Fin (n + 2)) :
    ComposableArrows C n := finiteChainFaceIndex k ⋙ F

/-- 概要：先頭以外の面の始点は元の始点。
方針：後続点を飛ばす埋め込みは0を固定する。規約：対象の実等式。
使われ方：Riehl–Verity §4.1の面と先頭の挿入の照合。 -/
lemma finiteChainFace_first {n : ℕ} (F : ComposableArrows C (n + 1)) (k : Fin (n + 1)) :
    (finiteChainFace F k.succ).obj 0 = F.obj 0 := by
  rfl

/-- 概要：先頭以外の面の尾部は、元の尾部の対応する面。
方針：実順序関手の全合成則で添字を照合する。規約：全関手の等式。
使われ方：Riehl–Verity §4.1の細分の再帰。 -/
lemma finiteChainFace_tail {n : ℕ} (F : ComposableArrows C (n + 2)) (k : Fin (n + 2)) :
    (finiteChainFace F k.succ).δ₀ = finiteChainFace F.δ₀ k := by
  change (Fin.succFunctor (n + 1) ⋙ finiteChainFaceIndex k.succ) ⋙ F =
    finiteChainFaceIndex k ⋙ (Fin.succFunctor (n + 2) ⋙ F)
  rw [finiteChainFaceIndex_succ]
  rfl

/-- 概要：先頭を挿入した実鎖の0番の面は元の実鎖。
方針：0を飛ばす関手は後続点への包含。規約：全射を含む等式。
使われ方：Riehl–Verity §4.1の再帰の基底。 -/
lemma finiteChainFace_precomp_zero {n : ℕ} (F : ComposableArrows C n) {A : C}
    (f : A ⟶ F.left) : finiteChainFace (F.precomp f) 0 = F := by
  rfl

/-- 概要：先頭二点を保つ面は先頭の挿入と可換。
方針：始点・尾部・最初の射を実際に比較する。規約：必要な対象の輸送も保持する。
使われ方：Riehl–Verity §4.1の指定面の再帰。 -/
lemma finiteChainFace_precomp_succ {n : ℕ} (F : ComposableArrows C (n + 1))
    {A : C} (f : A ⟶ F.left) (k : Fin (n + 1)) :
    finiteChainFace (F.precomp f) k.succ.succ =
      (finiteChainFace F k.succ).precomp (f ≫ eqToHom (finiteChainFace_first F k).symm) := by
  apply ComposableArrows.ext_succ
    (F := finiteChainFace (F.precomp f) k.succ.succ)
    (G := (finiteChainFace F k.succ).precomp (f ≫ eqToHom (finiteChainFace_first F k).symm))
    rfl (finiteChainFace_tail (F.precomp f) k.succ)
  have hfix : (1 : Fin (n + 3)) < k.succ.succ := by
    change 1 < k.val + 1 + 1
    omega
  simp [finiteChainFace, finiteChainFaceIndex, ComposableArrows.precomp,
    ComposableArrows.Precomp.map, Fin.succAbove, hfix]
  rfl

/-- 概要：二つの実射を先頭へ挿入し中間点を除くと合成の挿入へ戻る。
方針：始点・尾部・最初の合成の実表示を比較する。規約：全関手の等式。
使われ方：Riehl–Verity §4.1の指定面の基底。 -/
lemma finiteChainFace_precomp_pair {n : ℕ} (F : ComposableArrows C n)
    {A B : C} (q : A ⟶ B) (g : B ⟶ F.left) :
    finiteChainFace ((F.precomp g).precomp q) (1 : Fin (n + 3)) = F.precomp (q ≫ g) := by
  have ht : (finiteChainFace ((F.precomp g).precomp q) (1 : Fin (n + 3))).δ₀ = F :=
    (finiteChainFace_tail ((F.precomp g).precomp q) 0).trans (finiteChainFace_precomp_zero F g)
  apply ComposableArrows.ext_succ
    (F := finiteChainFace ((F.precomp g).precomp q) (1 : Fin (n + 3)))
    (G := F.precomp (q ≫ g)) rfl ht
  simp [finiteChainFace, finiteChainFaceIndex, ComposableArrows.precomp,
    ComposableArrows.Precomp.map, Fin.succAbove]
  rfl

end SerrePositivity.InfinityCategories.HA.Monads
