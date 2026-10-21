module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedMapBridges
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPostcompAlgebra
/-!
概要：明示端点の全関手射の合成・前後合成と交換則を証明する。
方針：同じ指定比較と射の値を保持し、全関手圏の等式を照合する。
規約：可逆性は追加しない。使われ方：元の κ の全射自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
lemma functorHomPostcomp_comp {X Y Z : SSet.{u}} (f g h : X ⟶ Y) (q : Y ⟶ Z)
    (a : FunctorHom f g) (b : FunctorHom g h) :
    functorHomPostcomp f h q (a ≫ b) =
      functorHomPostcomp f g q a ≫ functorHomPostcomp g h q b := by
  exact CategoryTheory.Functor.map_comp _ _ _
lemma functorHomPrecomp_comp {A X Y : SSet.{u}} (f g h : X ⟶ Y) (p : A ⟶ X)
    (a : FunctorHom f g) (b : FunctorHom g h) :
    functorHomPrecomp f h p (a ≫ b) =
      functorHomPrecomp f g p a ≫ functorHomPrecomp g h p b := by
  exact CategoryTheory.Functor.map_comp _ _ _
lemma functorHomPostcomp_postcomp {X Y Z W : SSet.{u}} (f g : X ⟶ Y)
    (q : Y ⟶ Z) (k : Z ⟶ W) (a : FunctorHom f g) :
    functorHomPostcomp (f ≫ q) (g ≫ q) k (functorHomPostcomp f g q a) =
      functorHomPostcomp f g (q ≫ k) a := by
  exact functorHom_postcomp_postcomp a q k
lemma functorHomPrecomp_precomp {A B X Y : SSet.{u}} (f g : X ⟶ Y)
    (p : B ⟶ X) (q : A ⟶ B) (a : FunctorHom f g) :
    functorHomPrecomp (p ≫ f) (p ≫ g) q (functorHomPrecomp f g p a) =
      functorHomPrecomp f g (q ≫ p) a := by
  exact functorHom_precomp_precomp a p q
lemma functorHomPrecomp_postcomp {A X Y Z : SSet.{u}} (f g : X ⟶ Y)
    (p : A ⟶ X) (q : Y ⟶ Z) (a : FunctorHom f g) :
    functorHomPostcomp (p ≫ f) (p ≫ g) q (functorHomPrecomp f g p a) =
      functorHomPrecomp (f ≫ q) (g ≫ q) p (functorHomPostcomp f g q a) := by
  exact functorHom_precomp_postcomp a p q
lemma functorIso_postcomp_hom_typed {X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (a : FunctorIso f g) (q : Y ⟶ Z) :
    (a.postcomp q).hom = functorHomPostcomp f g q a.hom := by
  exact F2.functorIso_postcomp_hom a q
lemma functorIso_precomp_hom_typed {A X Y : SSet.{u}} {f g : X ⟶ Y}
    (a : FunctorIso f g) (p : A ⟶ X) :
    (a.precomp p).hom = functorHomPrecomp f g p a.hom := by rfl
lemma functorHom_whisker_exchange_typed {X Y Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z] {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (a : FunctorHom f f') (b : FunctorHom g g') :
    functorHomPostcomp f f' g a ≫ functorHomPrecomp g g' f' b =
      functorHomPrecomp g g' f b ≫ functorHomPostcomp f f' g' a := by
  exact functorHom_whisker_exchange a b
end SerrePositivity.InfinityCategories
