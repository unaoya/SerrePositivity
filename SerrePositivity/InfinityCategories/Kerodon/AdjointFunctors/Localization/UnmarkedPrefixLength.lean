module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorSplit

/-!
# 最初の非指定生成矢より前の元の射列の長さ

概要：指定接頭列と最初の非指定生成矢による切断位置を、元の射列だけから回収する。
方針：元の cons に沿って、接頭列全体が指定である間だけ長さを増やす。
規約：恒等文字も元の射列の一文字として数える。
使われ方：最初の非指定生成矢による切断の一意性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

def initialLength {X : C} : ∀ {Y : C}, Quiver.Path X Y → ℕ
  | _, .nil => 0
  | _, .cons p f => by
    classical
    exact if W.paths p then if W f then p.length + 1 else p.length else initialLength p

lemma initialLength_first_split {X A B Y : C} (left : Quiver.Path X A) (e : A ⟶ B)
    (right : Quiver.Path B Y) (hl : W.paths left) (he : ¬ W e) :
    initialLength W (left.comp (e.toPath.comp right)) = left.length := by
  classical
  induction right with
  | nil => simp [Quiver.Hom.toPath, initialLength, hl, he]
  | cons right f ih =>
    have hn : ¬ W.paths (left.comp (e.toPath.comp right)) := by
      intro h
      exact he ((W.comp_mem_paths_iff.1 (W.comp_mem_paths_iff.1 h).2).1.2)
    simp only [Quiver.Path.comp_cons, initialLength, ite_eq_right hn, ih]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
