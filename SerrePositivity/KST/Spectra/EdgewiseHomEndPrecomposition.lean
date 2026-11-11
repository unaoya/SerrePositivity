module

public import SerrePositivity.KST.Spectra.EdgewiseParameterDiagram
public import SerrePositivity.KST.Spectra.WeightedParameterJointNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedConeEndPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralConeComparisonReflection

/-!
概要：Hom end の全パラメータの前合成作用を edgewise 化し、左右の射影と照合する。
方針：係数と Hom パラメータを同時に動かす end の自然性へ、二つの射影の可換式を渡す。
規約：元の共有の Hom 前合成作用を用いる。使われ方：coherent 錐の比較族の反転。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の非反転 Hom end の、共有の係数前合成から得る全パラメータ作用。 -/
def homEndPrecomposition (F : I ⥤ C) (x z : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z) ⊗ SimplicialCategory.sHom x z ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialHomPrecompositionDiagram F x z)

/-- 係数と Hom パラメータを edgewise 化した元の前合成作用。 -/
def edgewiseHomEndPrecomposition (F : I ⥤ C) (x z : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor) ⊗
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom x z) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (EdgewiseTensor.parameterDiagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialHomPrecompositionDiagram F x z))

/-- 共通解像の前合成作用と右 end 射影は、元の全 Hom パラメータの作用に厳密に可換。 -/
lemma edgewiseHomEndPrecomposition_right (F : I ⥤ C) (x z : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseRight (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z))
        ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (SimplicialCategory.sHom x z)) ≫ homEndPrecomposition F x z =
      edgewiseHomEndPrecomposition F x z ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseRight (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x)) :=
  WeightedParameterNaturality.joint_natural (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseRight (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseRight (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (SimplicialCategory.sHom x z))
    (EdgewiseTensor.parameterDiagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialHomPrecompositionDiagram F x z))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialHomPrecompositionDiagram F x z)
    (EdgewiseTensor.parameterDiagram_right (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialHomPrecompositionDiagram F x z))

/-- 共通解像の前合成作用と左 end 射影は、共有の反転した全 Hom の作用に厳密に可換。 -/
lemma edgewiseHomEndPrecomposition_left (F : I ⥤ C) (x z : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z))
        ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (SimplicialCategory.sHom x z)) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedConeEndPrecomposition F x z =
      edgewiseHomEndPrecomposition F x z ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x)) := by
  apply WeightedParameterNaturality.joint_natural
  intro i
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (SimplicialCategory.sHom z (F.obj i)) ⊗ₘ
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (SimplicialCategory.sHom x z)) ≫
      (Functor.Monoidal.μIso SSet.opFunctor (SimplicialCategory.sHom z (F.obj i))
        (SimplicialCategory.sHom x z)).hom ≫
      SSet.opFunctor.map ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialHomPrecompositionDiagram F x z).app i) = _
  exact EdgewiseTensor.parameterDiagram_left (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialHomPrecompositionDiagram F x z) i

end SerrePositivity.KST.Spectra
