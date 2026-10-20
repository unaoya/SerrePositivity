module

public import SerrePositivity.InfinityCategories.F1.QCatDiagramPrism
public import SerrePositivity.InfinityCategories.F1.FunctorSpaceCurrying
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramArrowEndpoints

/-!
概要：二点と底の積上の Cat∞ 値図式を、底上の関手の区間族へ移す。
方針：元の区間と底の積の射列を前合成し、同じ関手空間の curry を使う。
規約：区間の両端で元の端点制限を厳密に回収する。
使われ方：底全体の分類主写像の間の実際の比較の辺。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ二点と底の積上の図式を、底上の関手 ∞ 圏の区間族へ写す。 -/
def qCatDiagramArrowCurry (C : Type u) [Category.{u} C] :
    CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Fin 2 × C))) ⟶
      (ihom (Δ[1] : SSet.{u + 1})).obj
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))) :=
  (pre ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (Δ[1] : SSet.{u + 1})).hom ≫
    qCatDiagramPrismBase C)).app CatInfinity.{u} ≫
      functorSpaceCurryMap ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) Δ[1] CatInfinity.{u}

/-- 同じ区間族の各端点は、元の二点と底の積上の図式の同じ端点制限。 -/
lemma qCatDiagramArrowCurry_endpoint (C : Type u) [Category.{u} C] (i : Fin 2) :
    qCatDiagramArrowCurry C ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) =
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (quasicategoryDiagramEndpointIndex i C)))).app CatInfinity.{u} := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories
