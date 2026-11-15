module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.HomotopyIntervalCochain
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomFamilyEquiv
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalEndpoints
/-!
概要：与えた図式の鎖ホモトピーを指定された正規化区間で評価する。
方針：交換関手で図式Homに送り、既存テンソル–Hom同値を逆に使う。
規約：A06の本体。自由負鎖の同じ区間と標準パラメータ同型を保つ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type (max u v)} [CommRing A] {J : Type v} [SmallCategory J]
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)
/-- 元の図式のホモトピーを、同じ正規化単体区間で評価する。 -/
def normalizedIntervalHom {R S : J ⥤ Complex A} (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
    R ⊗ freeNegativeChainsDiagram (A := A) ((Functor.const J).obj
      ((SSet.uliftFunctor.{max u v,0}).obj (SSet.stdSimplex.{0}.obj ⦋1⦌))) ⟶ S :=
  (R ◁ (freeStandardSimplexParameterIso A J).hom.app ⦋1⦌) ≫
    (diagramTensorLinearHomEquiv R S
      ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
        (SSet.stdSimplex.obj ⦋1⦌))).symm
      (homotopyIntervalCochainMap A ((E).map f) ((E).map g) h)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
