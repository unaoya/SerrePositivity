module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorDoldKan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductSectionsHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductHomComparison

/-!
概要：元の自由正規化重みの図式 Hom 空間から、元の重み付き切断空間へ指定比較を作る。
方針：両側の全単体同型の間に、指定 AW・shuffle の前合成を置く。
規約：実際の二つの単体的射を定める。同値性は後続の証明で扱う。
使われ方：HA 1.2.4、G10 の指定 Hom 比較と native 切断への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CochainComplex
open SerrePositivity.HomologicalAlgebra SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type u} [SmallCategory J]
variable (X : J ⥤ SSet.{u}) (Q : J ⥤ CochainComplex (ModuleCat A) ℤ)
variable (φ : simplicialRingCoefficient.{u} →+* A)
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)

/-- 同じ指定 AW による実 Dold–Kan 空間から重み付き切断への比較。 -/
def normalizedWeightSectionMap :
    (truncatedDoldKanFunctor A).obj
      (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) X)) ((E).obj Q)) ⟶
        weightedSections X (Q ⋙ truncatedDoldKanFunctor A) :=
  (freeTensorDiagramHomIso A Q X).inv ≫
    (freeProductHomComparison A X (liftedStandardSimplexParameter J) φ).app Q ≫
      (freeProductSectionsHomIso A X Q).hom

/-- 同じ指定 shuffle による逆方向の実単体的射。 -/
def normalizedWeightSectionReverse :
    weightedSections X (Q ⋙ truncatedDoldKanFunctor A) ⟶
      (truncatedDoldKanFunctor A).obj
        (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) X)) ((E).obj Q)) :=
  (freeProductSectionsHomIso A X Q).inv ≫
    (freeProductHomReverse A X (liftedStandardSimplexParameter J) φ).app Q ≫
      (freeTensorDiagramHomIso A Q X).hom

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
