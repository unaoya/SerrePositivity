module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTypedMapBridges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoLiftedHom
/-!
概要：実包含後の比較と経路の反映を、同じ型付き全関手射で扱う。
方針：一般の関手空間で前後合成を回収し、元の指定値を保つ。
規約：可逆性は追加しない。使われ方：K-flat 合成比較の全射自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma functorIso_lifted_typed_hom_heq {A B X Y : SSet.{u}}
    {f g : A ⟶ X} {f' g' : B ⟶ Y}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (c' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (i : A ⟶ B) (j : X ⟶ Y)
    (hf : f ≫ j = i ≫ f') (hg : g ≫ j = i ≫ g')
    (he : HEq (c.postcomp j) (c'.precomp i)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g j c.hom) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f' g' i c'.hom) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_map_heq f g j c.hom).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_lifted_hom_heq c c' i j hf hg he).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_map_heq f' g' i c'.hom).symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
