module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt

/-!
# 端点も動く zigzag の縦比較

概要：全体の zigzag の部分区間では端点の縦射も動く。
方針：元の全頂点の弱同値と全列の可換性を保持し、端点の恒等条件を分離する。
規約：全体の端点を固定する際には元の first・last 条件を改めて検証する。
使われ方：関手的 pullback と pushout で置換した部分区間の貼り合わせ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
  {X Y X' Y' X'' Y'' : C}

structure MovingHom (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X' Y') where
  app : ∀ j, S.vertex j ⟶ T.vertex j
  app_mem : ∀ j, W (app j)
  comm : ∀ i, S.arrow i ≫ app (w.target i) = app (w.source i) ≫ T.arrow i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (MovingHom)


namespace MovingHom
variable {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X' Y'} {U : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X'' Y''}

@[ext] lemma ext (f g : MovingHom S T) (h : ∀ j, f.app j = g.app j) : f = g := by
  cases f
  cases g
  have h := funext h
  cases h
  rfl

def ofHom {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T) : MovingHom S T :=
  ⟨f.app, f.app_mem, f.comm⟩

def id [W.IsMultiplicative] (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) : MovingHom S S :=
  ⟨fun _ => 𝟙 _, fun _ => W.id_mem _, fun _ => by simp⟩

lemma id_first [W.IsMultiplicative] (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    HEq ((id S).app 0) (𝟙 X) :=
  (eqToHom_heq_id_dom _ _ S.first).symm.trans (eqToHom_heq_id_cod _ _ S.first)

lemma id_last [W.IsMultiplicative] (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    HEq ((id S).app (Fin.last w.length)) (𝟙 Y) :=
  (eqToHom_heq_id_dom _ _ S.last).symm.trans (eqToHom_heq_id_cod _ _ S.last)

def comp [W.IsMultiplicative] (f : MovingHom S T) (g : MovingHom T U) : MovingHom S U where
  app j := f.app j ≫ g.app j
  app_mem j := W.comp_mem _ _ (f.app_mem j) (g.app_mem j)
  comm i := by
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, ← Category.assoc]

lemma app_heq (f : MovingHom S T) {i j : Fin (w.length + 1)} (h : i = j) :
    HEq (f.app i) (f.app j) := by
  cases h
  rfl

def toHom {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} (f : MovingHom S T)
    (hf : f.app 0 = eqToHom (S.first.trans T.first.symm))
    (hl : f.app (Fin.last w.length) = eqToHom (S.last.trans T.last.symm)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T :=
  ⟨f.app, f.app_mem, hf, hl, f.comm⟩

lemma first_of_heq_id {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y'} (f : MovingHom S T)
    (h : HEq (f.app 0) (𝟙 X)) : f.app 0 = eqToHom (S.first.trans T.first.symm) := by
  have h' := (conj_eqToHom_iff_heq _ _ S.first T.first).2 h
  simpa only [Category.id_comp, eqToHom_trans] using h'

lemma last_of_heq_id {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X' Y} (f : MovingHom S T)
    (h : HEq (f.app (Fin.last w.length)) (𝟙 Y)) :
    f.app (Fin.last w.length) = eqToHom (S.last.trans T.last.symm) := by
  have h' := (conj_eqToHom_iff_heq _ _ S.last T.last).2 h
  simpa only [Category.id_comp, eqToHom_trans] using h'

end MovingHom
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
