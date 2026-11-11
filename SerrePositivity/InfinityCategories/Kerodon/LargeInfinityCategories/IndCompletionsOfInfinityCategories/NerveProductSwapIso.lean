module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps


/-!
概要：積の通常の添字の nerve を、順序を入れ替えた二つの nerve の積へ同定する。
方針：二つの射影と、二つの射列を同時に組にする逆を直接与える。
規約：射列の全ての面と退化を保つ。
使われ方：切断の積図式の大域比較を curry し、底の局所化へ戻す。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 積添字の nerve は、二つの nerve の入れ替えた積と標準同型。 -/
def nerveProductSwapIso (I J : Type u) [Category.{u} I] [Category.{u} J] :
    nerve (I × J) ≅ nerve J ⊗ nerve I where
  hom := lift (nerveMap (CategoryTheory.Prod.snd I J))
    (nerveMap (CategoryTheory.Prod.fst I J))
  inv := {
    app n := ↾fun (σ : (nerve J).obj n × (nerve I).obj n) ↦ σ.2.prod' σ.1
    naturality := by intros; rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    change (σ ⋙ CategoryTheory.Prod.fst I J).prod' (σ ⋙ CategoryTheory.Prod.snd I J) = σ
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    apply _root_.Prod.ext <;> rfl

/-- 同じ積の同型を空間値分類の宇宙へ持ち上げる。 -/
def uliftNerveProductSwapIso (I J : Type u) [Category.{u} I] [Category.{u} J] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (I × J)) ≅
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⊗
        (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) :=
  (SSet.uliftFunctor.{u + 1, u}).mapIso (nerveProductSwapIso I J) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} (nerve J) (nerve I)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
