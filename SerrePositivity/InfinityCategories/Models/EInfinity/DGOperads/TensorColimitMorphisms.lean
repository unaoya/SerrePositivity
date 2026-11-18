module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorColimit

/-!
模型。文献の定義との比較は後で
# 独立なテンソル図式の射を入力ごとの射で記述する

概要：Berger–Moerdijk §1 の自由代数の作用の降下で、余極限図式の射を各入力の置換へ分解する。
方針：直積圏の射の各成分を再帰的に取り出し、外部テンソル図式の射と比較する。
規約：空の直積と空のテンソルを含む。
使われ方：生成射の内側等変性から Schur テンソル図式上の余錐の自然性を得る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {J : Type} [SmallCategory J]

/-- 概要：独立な添字の直積圏の射を各入力の射族として読む（Berger–Moerdijk §1）。
方針：直積の先頭成分と残りの成分で再帰する。
規約：入力の対象は既存の有限族による表示を用いる。
使われ方：余極限の射の自然性を各入力の置換の等変性へ帰着する。 -/
def tensorIndexHomFamily : ∀ (n : ℕ) {j k : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex J n},
    (j ⟶ k) → ∀ i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily J n j i ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily J n k i
  | 0, _, _, _, i => Fin.elim0 i
  | n + 1, _, _, σ, i => Fin.cases σ.1 (fun i => tensorIndexHomFamily n σ.2 i) i

/-- 概要：底の添字圏で射の始域と終域が等しいなら直積圏でも等しい（Berger–Moerdijk §1）。
方針：各入力の射に底の圏の性質を適用して、直積の対象を同一視する。
規約：自己射が恒等射であるとは要求しない。
使われ方：有限全単射の骨格の各入力の arity が自然性の計算で変わらないことを示す。 -/
lemma tensorIndex_object_eq_of_hom
    (hJ : ∀ {j k : J}, (j ⟶ k) → j = k) (n : ℕ)
    {j k : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex J n} (σ : j ⟶ k) : j = k := by
  induction n with
  | zero => rcases j with ⟨⟨⟩⟩; rcases k with ⟨⟨⟩⟩; rfl
  | succ n ih =>
    rcases j with ⟨j, j'⟩
    rcases k with ⟨k, k'⟩
    exact Prod.ext (hJ σ.1) (ih σ.2)

variable {A : Type u} [CommRing A]

/-- 概要：外部テンソル図式の射は入力ごとの射の有限テンソルである（Berger–Moerdijk §1）。
方針：図式の対象と有限テンソルの比較を使い、各直積成分の射をテンソルする。
規約：対象の等式による移送を両辺で明示する。
使われ方：Schur 図式の自然性を全入力の同時置換の関係から証明する。 -/
lemma tensorIndexDiagram_map (F : J ⥤ Complex A) (n : ℕ) {j k : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex J n}
    (σ : j ⟶ k) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram F n).map σ ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram_obj F n k) =
      eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram_obj F n j) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => F.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexHomFamily n σ i)) := by
  induction n with
  | zero =>
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    rfl
  | succ n ih =>
    rcases j with ⟨j, j'⟩
    rcases k with ⟨k, k'⟩
    have hej : eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram_obj F (n + 1) (j, j')) =
        F.obj j ◁ eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram_obj F n j') := by rw [whiskerLeft_eqToHom]
    have hek : eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram_obj F (n + 1) (k, k')) =
        F.obj k ◁ eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram_obj F n k') := by rw [whiskerLeft_eqToHom]
    change ((F.map σ.1 ▷ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram F n).obj j') ≫
      (F.obj k ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram F n).map σ.2)) ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram_obj F (n + 1) (k, k')) =
      eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram_obj F (n + 1) (j, j')) ≫
        (F.map σ.1 ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => F.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexHomFamily n σ.2 i)))
    rw [← tensorHom_def, hej, hek, tensorHom_comp_whiskerLeft,
      whiskerLeft_comp_tensorHom, ih σ.2]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
