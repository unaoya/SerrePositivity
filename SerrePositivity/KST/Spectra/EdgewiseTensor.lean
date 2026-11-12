module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEdgewiseFunctor

/-!
概要：edgewise 共通解像のテンソル比較と左右射影の整合性。
方針：join からの二つの射を対にし、各次数で射の対の普遍性を使う。
規約：Kan 性を要求しない。使われ方：全 Hom パラメータの反転比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.EdgewiseTensor

/-- join からの二つの射を対にして作る edgewise のテンソル比較。 -/
def map (A B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (A ⊗ B) where
  app _ := ↾fun fg ↦ lift fg.1 fg.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro fg
    change lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map α.unop ≫ fg.1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map α.unop ≫ fg.2) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map α.unop ≫ lift fg.1 fg.2
    exact (comp_lift _ _ _).symm

/-- テンソル比較の右射影は二つの元の右射影の直積。 -/
@[reassoc]
lemma right (A B : SSet.{u}) : map A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (A ⊗ B) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight A ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight B := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro fg
  rfl

/-- テンソル比較の左射影は反転のモノイダル比較を通した二つの左射影。 -/
@[reassoc]
lemma left (A B : SSet.{u}) : map A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (A ⊗ B) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft A ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft B) ≫
      (Functor.Monoidal.μIso SSet.opFunctor A B).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro fg
  rfl

/-- テンソル比較は二つの単体集合の射に自然。 -/
@[reassoc]
lemma natural {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap g) ≫ map A' B' =
      map A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (f ⊗ₘ g) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro fg
  change lift (fg.1 ≫ f) (fg.2 ≫ g) = lift fg.1 fg.2 ≫ (f ⊗ₘ g)
  exact (lift_map _ _ _ _).symm

end SerrePositivity.KST.Spectra.EdgewiseTensor
