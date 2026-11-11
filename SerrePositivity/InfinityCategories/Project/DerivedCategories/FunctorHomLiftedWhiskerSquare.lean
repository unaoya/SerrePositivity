module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomPostcompAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomWhiskerHEq
/-!
概要：包含後の任意全関手射の一致を、前後合成の実正方形へ移す。
方針：同じ射の異種等式と全前後合成則を接続する。
規約：可逆性を仮定しない。使われ方：K-flat 合成比較の全射自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorHom_lifted_postcomp_square {A B X Y Z W : SSet.{u}}
    {f g : A ⟶ X} {f' g' : B ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (e' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g')
    (i : A ⟶ B) (j : X ⟶ Y) (q : X ⟶ Z) (k : Z ⟶ W) (q' : Y ⟶ W)
    (hf : i ≫ f' = f ≫ j) (hg : i ≫ g' = g ≫ j)
    (he : HEq ((SSet.mapHomotopyCategory ((ihom A).map j)).map e)
      ((SSet.mapHomotopyCategory ((pre i).app Y)).map e')) (hs : q ≫ k = j ≫ q') :
    HEq ((SSet.mapHomotopyCategory ((ihom A).map k)).map
      ((SSet.mapHomotopyCategory ((ihom A).map q)).map e))
      ((SSet.mapHomotopyCategory ((pre i).app W)).map
        ((SSet.mapHomotopyCategory ((ihom B).map q')).map e')) := by
  have h₁ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_postcomp e q k)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorMapHom_heq_of_functor_eq
    (congrArg (fun s => SSet.mapHomotopyCategory ((ihom A).map s)) hs) e
  have h₃ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_postcomp e j q').symm
  have h₄ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_heq
    ((SSet.mapHomotopyCategory ((ihom A).map j)).map e)
    ((SSet.mapHomotopyCategory ((pre i).app Y)).map e') hf.symm hg.symm he q'
  have h₅ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_postcomp e' i q')
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
lemma functorHom_lifted_precomp_square {A B X Y Z W : SSet.{u}}
    {f g : X ⟶ Y} {f' g' : Z ⟶ W}
    (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (e' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g')
    (i : X ⟶ Z) (j : Y ⟶ W) (p : A ⟶ X) (p' : B ⟶ Z) (k : A ⟶ B)
    (hf : i ≫ f' = f ≫ j) (hg : i ≫ g' = g ≫ j)
    (he : HEq ((SSet.mapHomotopyCategory ((ihom X).map j)).map e)
      ((SSet.mapHomotopyCategory ((pre i).app W)).map e')) (hs : p ≫ i = k ≫ p') :
    HEq ((SSet.mapHomotopyCategory ((ihom A).map j)).map
      ((SSet.mapHomotopyCategory ((pre p).app Y)).map e))
      ((SSet.mapHomotopyCategory ((pre k).app W)).map
        ((SSet.mapHomotopyCategory ((pre p').app W)).map e')) := by
  have h₁ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_postcomp e p j)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_heq
    ((SSet.mapHomotopyCategory ((ihom X).map j)).map e)
    ((SSet.mapHomotopyCategory ((pre i).app W)).map e') hf.symm hg.symm he p
  have h₃ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_precomp e' i p)
  have h₄ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorMapHom_heq_of_functor_eq
    (congrArg (fun s => SSet.mapHomotopyCategory ((pre s).app W)) hs) e'
  have h₅ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_precomp e' p' k).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
