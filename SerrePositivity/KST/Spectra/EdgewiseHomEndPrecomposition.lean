module

public import SerrePositivity.KST.Spectra.EdgewiseParameterDiagram
public import SerrePositivity.KST.Spectra.WeightedParameterJointNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConeEndPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.GeneralConeComparisonReflection

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
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の非反転 Hom end の、共有の係数前合成から得る全パラメータ作用。 -/
def homEndPrecomposition (F : I ⥤ C) (x z : C) :
    bousfieldKanHolim (simplicialHomDiagram F z) ⊗ SimplicialCategory.sHom x z ⟶
      bousfieldKanHolim (simplicialHomDiagram F x) :=
  weightedSectionsParameterMap (bousfieldKanWeight I) (simplicialHomPrecompositionDiagram F x z)

/-- 係数と Hom パラメータを edgewise 化した元の前合成作用。 -/
def edgewiseHomEndPrecomposition (F : I ⥤ C) (x z : C) :
    bousfieldKanHolim (simplicialHomDiagram F z ⋙ edgewiseSubdivisionFunctor) ⊗
        edgewiseSubdivision (SimplicialCategory.sHom x z) ⟶
      bousfieldKanHolim (simplicialHomDiagram F x ⋙ edgewiseSubdivisionFunctor) :=
  weightedSectionsParameterMap (bousfieldKanWeight I)
    (EdgewiseTensor.parameterDiagram (simplicialHomPrecompositionDiagram F x z))

/-- 共通解像の前合成作用と右 end 射影は、元の全 Hom パラメータの作用に厳密に可換。 -/
lemma edgewiseHomEndPrecomposition_right (F : I ⥤ C) (x z : C) :
    (weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseRight (simplicialHomDiagram F z))
        ⊗ₘ edgewiseRight (SimplicialCategory.sHom x z)) ≫ homEndPrecomposition F x z =
      edgewiseHomEndPrecomposition F x z ≫
        weightedSectionsMap (bousfieldKanWeight I)
          (diagramEdgewiseRight (simplicialHomDiagram F x)) :=
  WeightedParameterNaturality.joint_natural (bousfieldKanWeight I)
    (diagramEdgewiseRight (simplicialHomDiagram F z))
    (diagramEdgewiseRight (simplicialHomDiagram F x))
    (edgewiseRight (SimplicialCategory.sHom x z))
    (EdgewiseTensor.parameterDiagram (simplicialHomPrecompositionDiagram F x z))
    (simplicialHomPrecompositionDiagram F x z)
    (EdgewiseTensor.parameterDiagram_right (simplicialHomPrecompositionDiagram F x z))

/-- 共通解像の前合成作用と左 end 射影は、共有の反転した全 Hom の作用に厳密に可換。 -/
lemma edgewiseHomEndPrecomposition_left (F : I ⥤ C) (x z : C) :
    (weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseLeft (simplicialHomDiagram F z))
        ⊗ₘ edgewiseLeft (SimplicialCategory.sHom x z)) ≫ weightedConeEndPrecomposition F x z =
      edgewiseHomEndPrecomposition F x z ≫
        weightedSectionsMap (bousfieldKanWeight I)
          (diagramEdgewiseLeft (simplicialHomDiagram F x)) := by
  apply WeightedParameterNaturality.joint_natural
  intro i
  change (edgewiseLeft (SimplicialCategory.sHom z (F.obj i)) ⊗ₘ
    edgewiseLeft (SimplicialCategory.sHom x z)) ≫
      (Functor.Monoidal.μIso SSet.opFunctor (SimplicialCategory.sHom z (F.obj i))
        (SimplicialCategory.sHom x z)).hom ≫
      SSet.opFunctor.map ((simplicialHomPrecompositionDiagram F x z).app i) = _
  exact EdgewiseTensor.parameterDiagram_left (simplicialHomPrecompositionDiagram F x z) i

end SerrePositivity.KST.Spectra
