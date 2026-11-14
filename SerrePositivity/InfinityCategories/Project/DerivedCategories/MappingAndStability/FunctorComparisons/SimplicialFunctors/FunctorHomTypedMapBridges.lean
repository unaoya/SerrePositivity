module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomWhiskering
/-!
概要：型付き全関手射の前後合成を、同じ実 h Fun の射の作用へ照合する。
方針：一般の関手空間で同じ値を異種等式として固定する。
規約：可逆性は不要。使われ方：K-flat 合成比較の全射自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma functorHomPostcomp_map_heq {X Y Z : SSet.{u}}
    (f g : X ⟶ Y) (q : Y ⟶ Z) (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g q e)
      ((SSet.mapHomotopyCategory ((ihom X).map q)).map e) := by rfl
lemma functorHomPrecomp_map_heq {A X Y : SSet.{u}}
    (f g : X ⟶ Y) (p : A ⟶ X) (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g p e)
      ((SSet.mapHomotopyCategory ((pre p).app Y)).map e) := by rfl
lemma functorHomPostcomp_postcomp_map_heq {X Y Z W : SSet.{u}}
    (f g : X ⟶ Y) (q : Y ⟶ Z) (k : Z ⟶ W) (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (f ≫ q) (g ≫ q) k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g q e))
      ((SSet.mapHomotopyCategory ((ihom X).map k)).map
        ((SSet.mapHomotopyCategory ((ihom X).map q)).map e)) := by rfl
lemma functorHomPrecomp_postcomp_map_heq {A X Y Z : SSet.{u}}
    (f g : X ⟶ Y) (p : A ⟶ X) (q : Y ⟶ Z) (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (p ≫ f) (p ≫ g) q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g p e))
      ((SSet.mapHomotopyCategory ((ihom A).map q)).map
        ((SSet.mapHomotopyCategory ((pre p).app Y)).map e)) := by rfl
lemma functorHomPostcomp_precomp_map_heq {A X Y Z : SSet.{u}}
    (f g : X ⟶ Y) (p : A ⟶ X) (q : Y ⟶ Z) (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (f ≫ q) (g ≫ q) p (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g q e))
      ((SSet.mapHomotopyCategory ((pre p).app Z)).map
        ((SSet.mapHomotopyCategory ((ihom X).map q)).map e)) := by rfl
lemma functorHomPrecomp_precomp_map_heq {A B X Y : SSet.{u}}
    (f g : X ⟶ Y) (p : B ⟶ X) (q : A ⟶ B) (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (p ≫ f) (p ≫ g) q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g p e))
      ((SSet.mapHomotopyCategory ((pre q).app Y)).map
        ((SSet.mapHomotopyCategory ((pre p).app Y)).map e)) := by rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
