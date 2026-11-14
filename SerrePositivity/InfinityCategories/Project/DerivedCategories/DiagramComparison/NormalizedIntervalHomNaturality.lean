module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorHomNaturality
/-!
概要：指定正規化区間の図式ホモトピー評価の全射自然性。
方針：内部Homの前後合成自然性を同じテンソル–Hom同値で戻す。
規約：A06の自然性。区間・図式射・指定ホモトピーを保持する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type (max u v)} [CommRing A] {J : Type v} [SmallCategory J]
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)
/-- 指定された図式ホモトピーの元の前後合成。 -/
def normalizedIntervalHomotopyPrePost {R R' S S' : J ⥤ Complex A}
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
    Homotopy ((E).map (a ≫ f ≫ b)) ((E).map (a ≫ g ≫ b)) :=
  (h.compRight ((E).map b)).compLeft ((E).map a)
/-- 指定区間による図式ホモトピー評価は全図式射で前後合成と可換。 -/
theorem normalizedIntervalHom_naturality {R R' S S' : J ⥤ Complex A}
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
    (a ⊗ₘ 𝟙 (freeNegativeChainsDiagram (A := A) ((Functor.const J).obj
      ((SSet.uliftFunctor.{max u v,0}).obj (SSet.stdSimplex.{0}.obj ⦋1⦌))))) ≫
        normalizedIntervalHom f g h ≫ b =
      normalizedIntervalHom (a ≫ f ≫ b) (a ≫ g ≫ b)
        (normalizedIntervalHomotopyPrePost a b f g h) := by
  dsimp only [normalizedIntervalHom]
  rw [tensorHom_id]
  simp only [Category.assoc]
  erw [← whisker_exchange_assoc]
  apply congrArg (fun k => (R' ◁ (freeStandardSimplexParameterIso A J).hom.app ⦋1⦌) ≫ k)
  apply (diagramTensorLinearHomEquiv R' S'
    ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj ⦋1⦌))).injective
  rw [← Category.assoc]
  erw [diagramTensorLinearHomEquiv_naturality]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact homotopyIntervalCochainMap_naturality A ((E).map a) ((E).map b)
    ((E).map f) ((E).map g) h
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
