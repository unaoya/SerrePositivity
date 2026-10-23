module

public import SerrePositivity.InfinityCategories.F1.KanModels.KanEdgewiseFunctor

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
    edgewiseSubdivision A ⊗ edgewiseSubdivision B ⟶ edgewiseSubdivision (A ⊗ B) where
  app _ := ↾fun fg ↦ lift fg.1 fg.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro fg
    change lift (edgewiseWeight.map α.unop ≫ fg.1) (edgewiseWeight.map α.unop ≫ fg.2) =
      edgewiseWeight.map α.unop ≫ lift fg.1 fg.2
    exact (comp_lift _ _ _).symm

/-- テンソル比較の右射影は二つの元の右射影の直積。 -/
@[reassoc]
lemma right (A B : SSet.{u}) : map A B ≫ edgewiseRight (A ⊗ B) =
    edgewiseRight A ⊗ₘ edgewiseRight B := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro fg
  rfl

/-- テンソル比較の左射影は反転のモノイダル比較を通した二つの左射影。 -/
@[reassoc]
lemma left (A B : SSet.{u}) : map A B ≫ edgewiseLeft (A ⊗ B) =
    (edgewiseLeft A ⊗ₘ edgewiseLeft B) ≫
      (Functor.Monoidal.μIso SSet.opFunctor A B).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro fg
  rfl

/-- テンソル比較は二つの単体集合の射に自然。 -/
@[reassoc]
lemma natural {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    (edgewiseSubdivisionMap f ⊗ₘ edgewiseSubdivisionMap g) ≫ map A' B' =
      map A B ≫ edgewiseSubdivisionMap (f ⊗ₘ g) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro fg
  change lift (fg.1 ≫ f) (fg.2 ≫ g) = lift fg.1 fg.2 ≫ (f ⊗ₘ g)
  exact (lift_map _ _ _ _).symm

end SerrePositivity.KST.Spectra.EdgewiseTensor
