module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorHomNaturality
/-!
概要：図式Hom複体の始域射を同じコチェインの前合成で明示する。
方針：既存前後合成の後側を恒等射に固定する。
規約：IS-W2 A11のHpreの構成と既存自然性の特殊化。
使われ方：HA 1.2.4、元の重み射による指定Hom比較の自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type (max u v)} [CommRing A] {J : Type v} [SmallCategory J]
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)
/-- 始域の元の図式射による同じHom複体の前合成。 -/
def diagramHomSourceMap {P P' : J ⥤ Complex A} (a : P' ⟶ P) (Q : J ⥤ Complex A) :
    linearHomComplex A ((E).obj P) ((E).obj Q) ⟶ linearHomComplex A ((E).obj P') ((E).obj Q) :=
  intervalHomPrePost A (C := J ⥤ ModuleCat A) ((E).map a) (𝟙 ((E).obj Q))
/-- 元のテンソルHom同値の始域自然性の特殊化。 -/
theorem diagramTensorLinearHomEquiv_source {P P' Q : J ⥤ Complex A}
    (T : Complex A) (a : P' ⟶ P) (t : P ⊗ (Functor.const J).obj T ⟶ Q) :
    diagramTensorLinearHomEquiv P' Q T ((a ▷ (Functor.const J).obj T) ≫ t) =
      diagramTensorLinearHomEquiv P Q T t ≫ diagramHomSourceMap a Q := by
  have ht := diagramTensorLinearHomEquiv_naturality T a (𝟙 Q) t
  simpa only [Category.comp_id, CategoryTheory.Functor.map_id, diagramHomSourceMap] using ht
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
