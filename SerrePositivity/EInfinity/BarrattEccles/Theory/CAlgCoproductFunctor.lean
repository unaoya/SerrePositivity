module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoproductModel
public import SerrePositivity.EInfinity.BarrattEccles.CAlgVertexPresentation
public import SerrePositivity.EInfinity.Interface.Core
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.NerveMap

/-!
# CAlg の固定右因子との余積関手

## 概要
HA §3.2.4.7 の余積関手を、cofibrant な厳密余積の相対関手から作る。

## 方針
Hom の宇宙を同じ DK 入力にそろえ、局所化の coherent nerve の射を取る。

## 規約
ここでは関手と指定頂点での式を作り、余錐の余極限性は後で証明する。

## 使われ方
`coprodWith` の供給と、同じ厳密な余積包含による余錐の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits _root_.HomotopicalAlgebra SSet _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- The strict coproduct functor with the same cofibrant DK objects and lifted morphisms. -/
def cofibrantAlgebraDKCoprodWith (B : CofibrantAlgebra A) :
    (cofibrantAlgebraRelativeCategory A).category ⥤
      (cofibrantAlgebraRelativeCategory A).category :=
  (ULiftHom.down.{u, u + 1, u + 1} (C := CofibrantAlgebra A)) ⋙
    cofibrantAlgebraCoprodWith A B ⋙ (ULiftHom.up.{u, u + 1, u + 1} (C := CofibrantAlgebra A))

/-- Cofibrant-input coproducts preserve the specified weak equivalences of the DK input. -/
lemma cofibrantAlgebraDKCoprodWith_map_weak (B : CofibrantAlgebra A)
    {X Y : (cofibrantAlgebraRelativeCategory A).category} (g : X ⟶ Y)
    (hg : (cofibrantAlgebraRelativeCategory A).weakEquivalences g) :
    (cofibrantAlgebraRelativeCategory A).weakEquivalences
      ((cofibrantAlgebraDKCoprodWith A B).map g) := by
  let := modelCategory A
  let k := (cofibrantAlgebraDKInclusion A).map g
  have : IsCofibrant ((cofibrantAlgebraDKInclusion A).obj X) := cofibrantAlgebra_isCofibrant A X
  have : IsCofibrant ((cofibrantAlgebraDKInclusion A).obj Y) := cofibrantAlgebra_isCofibrant A Y
  have : WeakEquivalence k := (weakEquivalence_iff A k).mpr
    ((cofibrantAlgebraRelativeCategory_weakEquivalences_iff A g).mp hg)
  have h := modelCoprodWith_map_weakEquivalence ((cofibrantAlgebraInclusion A).obj B) k
  apply (cofibrantAlgebraRelativeCategory_weakEquivalences_iff A _).mpr
  exact (weakEquivalence_iff A _).mp h

/-- The actual relative coproduct functor used for the localization nerve. -/
def cofibrantAlgebraCoprodRelative (B : CofibrantAlgebra A) :
    cofibrantAlgebraRelativeCategory A ⟶ cofibrantAlgebraRelativeCategory A where
  functor := cofibrantAlgebraDKCoprodWith A B
  map _ _ g hg := cofibrantAlgebraDKCoprodWith_map_weak A B g hg

/-- The coproduct functor on CAlg with a fixed cofibrant right factor. -/
def cAlgCoprodWithModel (B : CofibrantAlgebra A) : CAlg_R A ⟶ CAlg_R A :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (cofibrantAlgebraCoprodRelative A B)

/-- The chosen functor uses exactly the strict coproduct on the specified vertex models. -/
lemma cAlgCoprodWithModel_vertex (B : CofibrantAlgebra A)
    (X : (cofibrantAlgebraRelativeCategory A).category) :
    atVertex (cAlgCoprodWithModel A B) (cAlgVertexEquiv A X) =
      cAlgVertexEquiv A ((cofibrantAlgebraDKCoprodWith A B).obj X) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_vertex (cofibrantAlgebraCoprodRelative A B) X

/-- The fixed-right-factor coproduct functor for an arbitrary vertex of CAlg. -/
def barrattEcclesCoprodWith (y : (CAlg_R A) _⦋0⦌) : CAlg_R A ⟶ CAlg_R A :=
  cAlgCoprodWithModel A ((cAlgVertexEquiv A).symm y)

end SerrePositivity.EInfinity.BarrattEccles
