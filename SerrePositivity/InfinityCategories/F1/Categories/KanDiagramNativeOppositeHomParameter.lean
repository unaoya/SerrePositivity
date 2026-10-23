module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseDualityLeftEndpoint
public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramOppositeHomIntervalComparison

/-!
概要：反転後の左区間族を、元の strict Hom の右端パラメーターから直接表す。
方針：双対後の左端の式と二重反転の逆同型により係数反転を元の Hom へ戻す。
規約：左右の端点射影を同一視せず、表示変更の射を明示する。
使われ方：weighted Hom の右端作用と同じパラメーター上で pointed prism を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

variable {I : Type u} [SmallCategory I]

/-- 元の Hom を、反転した二図式の左 Hom の係数へ直接写す。 -/
def kanDiagramNativeOppositeHomParameter (F G : KanDiagramObject I) :
    SimplicialCategory.sHom F G ⟶
      (strictDiagramMappingSpace
        ((F.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget)
        ((G.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget)).op :=
  (SSet.opFunctorCompOpFunctorIso.app (SimplicialCategory.sHom F G)).inv ≫
    SSet.opFunctor.map
      (strictDiagramOppositeHom (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget))

/-- 反転後の左端は、元の右端と同じ native な係数反転の射の合成。 -/
lemma kanDiagramOppositeHomParameter_left (F G : KanDiagramObject I) :
    kanDiagramOppositeHomParameter F G ≫ edgewiseLeft _ =
      edgewiseRight (SimplicialCategory.sHom F G) ≫
        kanDiagramNativeOppositeHomParameter F G := by
  rw [kanDiagramOppositeHomParameter, Category.assoc, edgewiseLeft_naturality,
    ← Category.assoc, edgewiseDuality_left, Category.assoc]
  rfl

/-- 同じ左区間族の共通パラメーターは、weighted 作用が用いる元の Hom の右端。 -/
lemma kanDiagramOppositeLeftHomInterval_eq_native (F G : KanDiagramObject I) :
    kanDiagramOppositeLeftHomInterval F G =
      (SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight (SimplicialCategory.sHom F G)) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (kanDiagramNativeOppositeHomParameter F G) ≫
          kanEnrichedDiagramLeftHomInterval (kanDiagramUniversalEnriched I)
            (show KanDiagramObject I from ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
            (show KanDiagramObject I from ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩) rfl rfl := by
  rw [kanDiagramOppositeLeftHomInterval, ← Category.assoc, ← Functor.map_comp,
    kanDiagramOppositeHomParameter_left, Functor.map_comp, Category.assoc]

/-- 一成分での native な係数反転は、同じ成分の内部 Hom の二重反転と反転同型。 -/
lemma kanDiagramNativeOppositeHomParameter_component
    (F G : KanDiagramObject I) (i : I) :
    kanDiagramNativeOppositeHomParameter F G ≫
      SSet.opFunctor.map (strictDiagramMappingComponent
        ((F.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget)
        ((G.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget) i) =
    strictDiagramMappingComponent (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i ≫
      (SSet.opFunctorCompOpFunctorIso.app
        ((ihom (F.val.obj i).obj).obj (G.val.obj i).obj)).inv ≫
      SSet.opFunctor.map
        (HomotopyLimits.oppositeInternalHomIso (F.val.obj i).obj (G.val.obj i).obj).hom := by
  let c := strictDiagramMappingComponent
    (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i
  have hc := strictDiagramOppositeHom_component
    (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i
  have h := congrArg SSet.opFunctor.map hc
  have hn := SSet.opFunctorCompOpFunctorIso.inv.naturality c
  change c ≫ (SSet.opFunctorCompOpFunctorIso.app
      ((ihom (F.val.obj i).obj).obj (G.val.obj i).obj)).inv =
    (SSet.opFunctorCompOpFunctorIso.app (SimplicialCategory.sHom F G)).inv ≫
      SSet.opFunctor.map (SSet.opFunctor.map c) at hn
  have h' := congrArg
    (fun f => (SSet.opFunctorCompOpFunctorIso.app (SimplicialCategory.sHom F G)).inv ≫ f) h
  simp only [Functor.map_comp] at h'
  have hn' := congrArg (fun f => f ≫ SSet.opFunctor.map
    (HomotopyLimits.oppositeInternalHomIso (F.val.obj i).obj (G.val.obj i).obj).hom) hn
  simp only [Category.assoc] at hn'
  calc
    _ = (SSet.opFunctorCompOpFunctorIso.app (SimplicialCategory.sHom F G)).inv ≫
        SSet.opFunctor.map (SSet.opFunctor.map c) ≫ SSet.opFunctor.map
          (HomotopyLimits.oppositeInternalHomIso (F.val.obj i).obj (G.val.obj i).obj).hom := by
      convert h' using 1 <;> rfl
    _ = _ := by
      convert hn'.symm using 1

end SerrePositivity.InfinityCategories
