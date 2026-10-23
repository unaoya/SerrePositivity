module

public import SerrePositivity.InfinityCategories.F1.Transport.NativePointHomCoefficientAction
public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramReflectedHomPostcomposition
public import SerrePositivity.InfinityCategories.F1.KanModels.KanOppositeCoefficients

/-!
概要：元の strict Kan 変換の native な反転後合成は、標準係数を介して元の評価と可換。
方針：反転後合成の uncurry と native な係数射の成分公式を、一点 Hom の合成則へ渡す。
規約：同じ全 Hom パラメーターを使い、独立な比較写像に置き換えない。
使われ方：共通 weighted prism の終点の作用の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 図式の標準係数同型の成分は、元の各対象の一点 Hom の標準係数同型の逆。 -/
lemma oppositePointHomDiagramIso_hom_app {I : Type u} [SmallCategory I]
    (F : I ⥤ KanObject.{u}) (i : I) :
    (oppositePointHomDiagramIso F).hom.app i = (pointedSpaceLeftCoefficientIso (F.obj i)).inv :=
  rfl

/-- 元の全変換の native な反転後合成は、標準係数を介して元の同じ成分の評価と可換。 -/
lemma kanDiagramNativePointHomAction_coefficient {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (i : I) :
    uncurry ((kanDiagramNativeOppositeHomParameter F G ≫
      kanDiagramReflectedHomPostcomposition
        (show KanDiagramObject I from ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
        (show KanDiagramObject I from ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩) pointKanObject) ≫
      strictDiagramMappingComponent
        (simplicialHomDiagram (F.val ⋙ kanObjectOpFunctor) pointKanObject ⋙ SSet.opFunctor)
        (simplicialHomDiagram (G.val ⋙ kanObjectOpFunctor) pointKanObject ⋙ SSet.opFunctor) i) ≫
      (oppositePointHomDiagramIso G.val).hom.app i =
    ((oppositePointHomDiagramIso F.val).hom.app i ▷ SimplicialCategory.sHom F G) ≫
      uncurry (strictDiagramMappingComponent (F.val ⋙ kanObjectForget)
        (G.val ⋙ kanObjectForget) i) := by
  let F' : KanDiagramObject I := ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩
  let G' : KanDiagramObject I := ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩
  let ψ := kanDiagramNativeOppositeHomParameter F G
  let A := (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj (F.val.obj i))).op
  let f := strictDiagramMappingComponent (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i
  rw [oppositePointHomDiagramIso_hom_app, oppositePointHomDiagramIso_hom_app,
    Category.assoc, uncurry_natural_left]
  calc
    _ = ((A ◁ ψ) ≫ ((A ◁ SSet.opFunctor.map (strictDiagramMappingComponent
          (F'.val ⋙ kanObjectForget) (G'.val ⋙ kanObjectForget) i)) ≫
        (opTensorIso _ _).hom ≫ SSet.opFunctor.map
          (eComp SSet pointKanObject (F'.val.obj i) (G'.val.obj i)))) ≫
          (pointedSpaceLeftCoefficientIso (G.val.obj i)).inv :=
      congrArg (fun k => ((A ◁ ψ) ≫ k) ≫
        (pointedSpaceLeftCoefficientIso (G.val.obj i)).inv)
          (kanDiagramReflectedHomPostcomposition_uncurry F' G' pointKanObject i)
    _ = ((A ◁ (ψ ≫ SSet.opFunctor.map (strictDiagramMappingComponent
          (F'.val ⋙ kanObjectForget) (G'.val ⋙ kanObjectForget) i))) ≫
        (opTensorIso _ _).hom ≫ SSet.opFunctor.map
          (eComp SSet pointKanObject (F'.val.obj i) (G'.val.obj i))) ≫
          (pointedSpaceLeftCoefficientIso (G.val.obj i)).inv := by
      simp only [whiskerLeft_comp, Category.assoc]
    _ = _ := by
      rw [show ψ ≫ SSet.opFunctor.map (strictDiagramMappingComponent
          (F'.val ⋙ kanObjectForget) (G'.val ⋙ kanObjectForget) i) =
        f ≫ (SSet.opFunctorCompOpFunctorIso.app
          ((ihom (F.val.obj i).obj).obj (G.val.obj i).obj)).inv ≫
          SSet.opFunctor.map (oppositeInternalHomIso (F.val.obj i).obj
            (G.val.obj i).obj).hom from kanDiagramNativeOppositeHomParameter_component F G i]
      exact nativePointHomComposition_coefficient f

end SerrePositivity.InfinityCategories
