module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.F1B.Adjunction.Adjunction
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomCorrespondence
public import SerrePositivity.InfinityCategories.F1B.Localization.ReflectiveIdempotence

/-!
分割で生成：docstring を書き直すこと
概要：反射の左関手は、右随伴の像を終点とする全関手圏の Hom を保つ。
方針：逆 adjunct は左関手の像と可逆余単位の合成なので、余単位を相殺する。
規約：任意の quasicategory パラメータでの主張。使われ方：Tamme の写像空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (hG : IsFullyFaithful G)

include hG in
lemma reflectiveCounitHom_isIso : IsIso a.counitHom :=
  a.counitHom_isIso_of_postcompFullyFaithful (hG.postcompose Y).toHoFullyFaithful

/-- 右随伴の像への Hom の、元の左関手による後合成を表す全単射。 -/
def reflectiveTargetHomEquiv {A : SSet.{u}} [Quasicategory A]
    (U : A ⟶ X) (V : A ⟶ Y) :
    FunctorHom U (V ≫ G) ≃ FunctorHom (U ≫ F) ((V ≫ G) ≫ F) := by
  have := reflectiveCounitHom_isIso a hG
  let ε := (hoFunctor.map ((pre V).app Y)).toFunctor.map a.counitHom
  have : IsIso ε := inferInstance
  exact (a.homEquiv U V).symm.trans ((Iso.refl _).homCongr (asIso ε).symm)

end SerrePositivity.KST.LocalizingInvariants
