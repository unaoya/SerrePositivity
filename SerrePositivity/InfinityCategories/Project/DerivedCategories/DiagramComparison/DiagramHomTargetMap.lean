module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorHomNaturality
/-!
概要：図式Hom複体の標的射を、既存の前後合成から明示する。
方針：前側を恒等射に固定し、同じコチェインと微分を使う。
規約：A10の型推論のための証明分割。計算上限を変えない。
使われ方：HA 1.2.4、指定自由テンソルHomの標的自然性。
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
/-- 指定図式Homの標的における元の全射の作用。 -/
def diagramHomTargetMap (P : J ⥤ Complex A) {Q Q' : J ⥤ Complex A} (f : Q ⟶ Q') :
    linearHomComplex A ((E).obj P) ((E).obj Q) ⟶ linearHomComplex A ((E).obj P) ((E).obj Q') :=
  intervalHomPrePost A (C := J ⥤ ModuleCat A) (R := (E).obj P) (R' := (E).obj P)
    (S := (E).obj Q) (S' := (E).obj Q') (𝟙 _) ((E).map f)
/-- 元の図式テンソルHom同値の標的自然性の特殊化。 -/
theorem diagramTensorLinearHomEquiv_postcomp (P : J ⥤ Complex A)
    {Q Q' : J ⥤ Complex A} (T : Complex A) (t : P ⊗ (Functor.const J).obj T ⟶ Q)
    (f : Q ⟶ Q') :
    diagramTensorLinearHomEquiv P Q' T (t ≫ f) =
      diagramTensorLinearHomEquiv P Q T t ≫ diagramHomTargetMap P f := by
  have ht := diagramTensorLinearHomEquiv_naturality T (𝟙 P) f t
  simpa only [CategoryTheory.Functor.map_id, id_whiskerRight, Category.id_comp,
    diagramHomTargetMap] using ht
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
