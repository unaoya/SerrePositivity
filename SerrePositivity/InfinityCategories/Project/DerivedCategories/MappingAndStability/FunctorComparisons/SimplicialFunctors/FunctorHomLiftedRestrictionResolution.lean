module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FunctorHomPostcompAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomWhiskerHEq
/-!
概要：指定された全関手射の制限と比較を、元の値を保って照合する。
方針：同じ端点・全関手圏の作用・実包含後の一致を使う。
規約：射の可逆性と追加の平坦性は不要。使われ方：ξ と κ の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorHom_lifted_restriction_resolution_heq {A B C D S Y : SSet.{u}}
    {f g : A ⟶ B} {f' g' : C ⟶ D}
    (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (e' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g')
    (i : A ⟶ C) (j : B ⟶ D) (p : S ⟶ A) (p' : S ⟶ C) (q : D ⟶ Y)
    (hf : i ≫ f' = f ≫ j) (hg : i ≫ g' = g ≫ j)
    (he : HEq ((SSet.mapHomotopyCategory ((ihom A).map j)).map e)
      ((SSet.mapHomotopyCategory ((pre i).app D)).map e'))
    (hs : p ≫ i = p') :
    HEq ((SSet.mapHomotopyCategory ((pre p).app Y)).map
      ((SSet.mapHomotopyCategory ((ihom A).map (j ≫ q))).map e))
      ((SSet.mapHomotopyCategory ((ihom S).map q)).map
        ((SSet.mapHomotopyCategory ((pre p').app D)).map e')) := by
  subst p'
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_heq
    ((SSet.mapHomotopyCategory ((pre i).app D)).map e')
    ((SSet.mapHomotopyCategory ((ihom A).map j)).map e) hf hg he.symm p
  have hh := hp.symm.trans (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_precomp e' i p))
  have hF : (p ≫ i) ≫ f' = p ≫ (f ≫ j) := by rw [Category.assoc, hf]
  have hG : (p ≫ i) ≫ g' = p ≫ (g ≫ j) := by rw [Category.assoc, hg]
  have hq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_heq
    ((SSet.mapHomotopyCategory ((pre p).app D)).map
      ((SSet.mapHomotopyCategory ((ihom A).map j)).map e))
    ((SSet.mapHomotopyCategory ((pre (p ≫ i)).app D)).map e')
    hF.symm hG.symm hh q
  have hpq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_heq
    ((SSet.mapHomotopyCategory ((ihom A).map q)).map
      ((SSet.mapHomotopyCategory ((ihom A).map j)).map e))
    ((SSet.mapHomotopyCategory ((ihom A).map (j ≫ q))).map e)
    (Category.assoc f j q) (Category.assoc g j q)
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_postcomp e j q)) p
  have hx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_postcomp
    (f := f ≫ j) (g := g ≫ j)
    ((SSet.mapHomotopyCategory ((ihom A).map j)).map e) p q
  exact hpq.symm.trans ((heq_of_eq hx.symm).trans hq)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
