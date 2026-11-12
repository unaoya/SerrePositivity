module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightTotalComparison
public import SerrePositivity.HomologicalAlgebra.LinearWeightEndTotalParameters
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex

/-!
概要：標準重みの線形 end と元の積 Tot の指定比較を、全係数図式の自然同型にする。
方針：同じ自由生成元の評価で余鎖二重複体の自然性を示し、積全複体へ移す。
規約：比較の前向き射は既存の standardWeightEndTotalIso の射そのもの。
使われ方：HA 1.2.4、G10 の元の余単体図式の射と指定比較との両立。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 同じ標準重みの余鎖比較は、元の係数図式の全射に自然。 -/
theorem standardWeightEndCochainIso_naturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (linearWeightEndCochainMap A
      (Functor.whiskerLeft (opOpEquivalence SimplexCategory).functor f)).app
        (op (AlternatingFaceMapComplex.obj (standardSimplexWeight (ModuleCat.of A A)))) ≫
          (standardWeightEndCochainIso Y).hom =
      (standardWeightEndCochainIso X).hom ≫ (alternatingCofaceMapComplex (Complex A)).map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

/-- 元の全余単体図式を、同じ標準鎖重みの線形 end の積全複体へ送る関手。 -/
def standardWeightEndTotalFunctor : CosimplicialObject (Complex A) ⥤ Complex A :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖᵒᵖ SimplexCategory (Complex A)).obj
      (opOpEquivalence SimplexCategory).functor ⋙
    linearWeightEndTotalFamily A ⋙
    (evaluation (ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℕ)ᵒᵖ (Complex A)).obj
      (op (AlternatingFaceMapComplex.obj (standardSimplexWeight (ModuleCat.of A A))))

/-- 同じ標準重みの指定比較を、元の積 Tot への全関手の自然同型として返す。 -/
def standardWeightEndTotalNatIso :
    standardWeightEndTotalFunctor (A := A) ≅ productTotalFunctor A :=
  NatIso.ofComponents standardWeightEndTotalIso (by
    intro X Y f
    have hm : standardWeightEndTotalFunctor.map f =
        (cochainProductTotalizationFunctor (ModuleCat.{u} A)).map
          ((linearWeightEndCochainMap A
            (Functor.whiskerLeft (opOpEquivalence SimplexCategory).functor f)).app
            (op (AlternatingFaceMapComplex.obj (standardSimplexWeight (ModuleCat.of A A))))) := by
      rfl
    have hr : (productTotalFunctor A).map f =
        (cochainProductTotalizationFunctor (ModuleCat.{u} A)).map
          ((alternatingCofaceMapComplex (Complex A)).map f) := by
      rfl
    rw [hm, hr]
    exact (Functor.map_comp _ _ _).symm.trans
      ((congrArg (cochainProductTotalizationFunctor (ModuleCat.{u} A)).map
        (standardWeightEndCochainIso_naturality f)).trans (Functor.map_comp _ _ _)))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
