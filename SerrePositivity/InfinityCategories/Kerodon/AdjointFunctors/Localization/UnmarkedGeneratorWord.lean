module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths

/-!
# 元の射列の非指定生成文字列

概要：元の自由射列から W の生成文字だけを消し、残りの全生成矢と端点を記録する。
方針：元の Path の cons を右への一文字追加として処理する。
規約：非指定文字は Quiver.Total C により元の始域・終域・射そのものを保持する。
使われ方：指定縦射の可換正方形で不変な hammock の分解位置。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C]

def letters {X : C} : ∀ {Y : C}, Quiver.Path X Y → List (Quiver.Total C)
  | _, .nil => []
  | _, @Quiver.Path.cons _ _ _ Y Z p f => letters p ++ [⟨Y, Z, f⟩]

variable (W : MorphismProperty C)

def erase {X : C} : ∀ {Y : C}, Quiver.Path X Y → List (Quiver.Total C)
  | _, .nil => []
  | _, @Quiver.Path.cons _ _ _ Y Z p f => by
    classical
    exact if W f then erase p else erase p ++ [⟨Y, Z, f⟩]

lemma letters_comp {X Y Z : C} (p : Quiver.Path X Y) (q : Quiver.Path Y Z) :
    letters (p.comp q) = letters p ++ letters q := by
  induction q with
  | nil => simp [letters]
  | cons q f ih => simp only [Quiver.Path.comp_cons, letters, ih, List.append_assoc]

lemma erase_comp {X Y Z : C} (p : Quiver.Path X Y) (q : Quiver.Path Y Z) :
    erase W (p.comp q) = erase W p ++ erase W q := by
  classical
  induction q with
  | nil => simp [erase]
  | cons q f ih =>
    by_cases hf : W f <;> simp [Quiver.Path.comp_cons, erase, hf, ih, List.append_assoc]

lemma erase_eq_filter {X Y : C} (p : Quiver.Path X Y) :
    erase W p = (letters p).filter (fun t => by classical exact decide (¬ W t.hom)) := by
  classical
  induction p with
  | nil => rfl
  | cons p f ih => by_cases hf : W f <;> simp [letters, erase, hf, ih]

lemma erase_eq_nil_iff {X Y : C} (p : Quiver.Path X Y) :
    erase W p = [] ↔ W.paths p := by
  classical
  induction p with
  | nil => simp [erase]
  | cons p f ih =>
    by_cases hf : W f <;> simp [erase, hf, MorphismProperty.cons_mem_paths_iff, ih]

lemma erase_marked {X Y : C} (p : Quiver.Path X Y) (hp : W.paths p) : erase W p = [] :=
  (erase_eq_nil_iff W p).2 hp

lemma erase_square {X Y X' Y' : C} (p : Quiver.Path X Y) (q : Quiver.Path X' Y')
    (u : Quiver.Path X X') (v : Quiver.Path Y Y') (hu : W.paths u) (hv : W.paths v)
    (h : p.comp v = u.comp q) : erase W p = erase W q := by
  have he := congrArg (erase W) h
  simpa only [erase_comp, erase_marked W u hu, erase_marked W v hv,
    List.append_nil, List.nil_append] using he

lemma erase_eqToHom {X Y : Paths C} (h : X = Y) : erase W (eqToHom h) = [] := by
  cases h
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
