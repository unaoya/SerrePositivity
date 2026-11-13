module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomTypedMapBridges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FunctorHomPostcompAlgebra
/-!
概要：明示端点の全関手射の合成・前後合成と交換則を証明する。
方針：同じ指定比較と射の値を保持し、全関手圏の等式を照合する。
規約：可逆性は追加しない。使われ方：元の κ の全射自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma functorHomPostcomp_comp {X Y Z : SSet.{u}} (f g h : X ⟶ Y) (q : Y ⟶ Z)
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g h) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f h q (a ≫ b) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g q a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp g h q b := by
  exact CategoryTheory.Functor.map_comp _ _ _
lemma functorHomPrecomp_comp {A X Y : SSet.{u}} (f g h : X ⟶ Y) (p : A ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g h) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f h p (a ≫ b) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g p a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp g h p b := by
  exact CategoryTheory.Functor.map_comp _ _ _
lemma functorHomPostcomp_postcomp {X Y Z W : SSet.{u}} (f g : X ⟶ Y)
    (q : Y ⟶ Z) (k : Z ⟶ W) (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (f ≫ q) (g ≫ q) k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g q a) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g (q ≫ k) a := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_postcomp a q k
lemma functorHomPrecomp_precomp {A B X Y : SSet.{u}} (f g : X ⟶ Y)
    (p : B ⟶ X) (q : A ⟶ B) (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (p ≫ f) (p ≫ g) q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g p a) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g (q ≫ p) a := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_precomp a p q
lemma functorHomPrecomp_postcomp {A X Y Z : SSet.{u}} (f g : X ⟶ Y)
    (p : A ⟶ X) (q : Y ⟶ Z) (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (p ≫ f) (p ≫ g) q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g p a) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (f ≫ q) (g ≫ q) p (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g q a) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_postcomp a p q
lemma functorIso_postcomp_hom_typed {X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (q : Y ⟶ Z) :
    (a.postcomp q).hom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g q a.hom := by
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom a q
lemma functorIso_precomp_hom_typed {A X Y : SSet.{u}} {f g : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : A ⟶ X) :
    (a.precomp p).hom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g p a.hom := by rfl
lemma functorHom_whisker_exchange_typed {X Y Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z] {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f f') (b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g g') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f f' g a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp g g' f' b =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp g g' f b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f f' g' a := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_whisker_exchange a b
end SerrePositivity.InfinityCategories.Project.DerivedCategories
