module

public import SerrePositivity.KST.Spectra.WeightedConeTriangleEdgewise
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedNerveSections
public import SerrePositivity.InfinityCategories.HomotopyLimits.GeneralConeComparisonReflection

/-!
概要：共通 edgewise 解像上の BK 切断から得る錐の三角形を、元の解像の左辺で計算する。
方針：元の over 重みの初区間の像で係数を評価し、左射影と反転の読取りを消去する。
規約：底の元の射列と解像切断を保持。使われ方：元の円評価錐全体と BK 錐の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の解像切断の反転比較が作る三角形の Hom 経路は、元の解像単体の左辺そのもの。 -/
lemma weightedEdgewiseSection_triangleTrace (F : I ⥤ C) (x : C)
    (η : bousfieldKanWeight I ⟶ simplicialHomDiagram F x ⋙ edgewiseSubdivisionFunctor)
    (σ : ComposableArrows I 1) :
    triangleTrace (weightedConeSimplex F x
      (prefixOverWeight σ ≫ Functor.whiskerLeft σ
        (η ≫ diagramEdgewiseLeft (simplicialHomDiagram F x)))) =
      (stdSimplex.opIso ⦋1⦌).inv ≫ joinInl (Δ[1] : SSet.{u}).op Δ[1] ≫
        SSet.yonedaEquiv ((prefixOverWeight σ).app (1 : Fin 2) ≫
          η.app (σ.obj (1 : Fin 2))) := by
  rw [weightedConeSimplex_triangleTrace]
  change (stdSimplex.opIso ⦋1⦌).inv ≫ reflectedSimplexMap
    (((prefixOverWeight σ).app (1 : Fin 2) ≫ η.app (σ.obj (1 : Fin 2))) ≫
      edgewiseLeft (SimplicialCategory.sHom x (F.obj (σ.obj (1 : Fin 2))))) = _
  have hτ :
      ((prefixOverWeight σ).app (1 : Fin 2) ≫ η.app (σ.obj (1 : Fin 2))) ≫
          edgewiseLeft (SimplicialCategory.sHom x (F.obj (σ.obj (1 : Fin 2)))) =
        SSet.yonedaEquiv.symm
          ((edgewiseLeft (SimplicialCategory.sHom x (F.obj (σ.obj (1 : Fin 2))))).app
            (Opposite.op ⦋1⦌) (SSet.yonedaEquiv
              ((prefixOverWeight σ).app (1 : Fin 2) ≫ η.app (σ.obj (1 : Fin 2))))) := by
    rw [← SSet.yonedaEquiv_symm_comp, Equiv.symm_apply_apply]
  rw [hτ, edgewiseLeft_coefficient_unreverse]
  rfl

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
