module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomTypedMapBridges
/-!
概要：包含後の射と自然性の等式を、明示端点の全関手射で照合する。
方針：元の射の像を一般の前後合成で保持する。
規約：可逆性は追加しない。使われ方：K-flat 合成比較の全射自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma functorHom_two_three_typed_whisker_eq {X Y Z : SSet.{u}}
    (f f' : X ⟶ Y) (g g' : Y ⟶ Z) (t t' : X ⟶ Z)
    (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f f') (d : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g g')
    (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (f ≫ g) t) (r : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom t t') (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (f' ≫ g') t')
    (he : c ≫ r = (SSet.mapHomotopyCategory ((ihom X).map g)).map e ≫
      (SSet.mapHomotopyCategory ((pre f').app Z)).map d ≫ a) :
    c ≫ r = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f f' g e ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp g g' f' d ≫ a := by
  exact he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
