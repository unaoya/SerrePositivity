module

public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictDiagramOppositeHom
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedHomInterval
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOppositeHomEquivalence

/-!
概要：反転した二図式の Hom の共通解像へ、元の全 Hom を厳密に写す。
方針：係数反転の射と edgewise の双対を合成し、右端を元の豊穣作用と照合する。
規約：strict な変換空間の Kan 性は要求しない。
使われ方：既存の左右区間比較を、実際の反転 unstraightening の作用に接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

variable {I : Type u} [SmallCategory I]

/-- 元の全 Hom の共通解像を、反転した二図式間の全 Hom の共通解像へ写す。 -/
def kanDiagramOppositeHomParameter (F G : KanDiagramObject I) :
    edgewiseSubdivision (SimplicialCategory.sHom F G) ⟶
      edgewiseSubdivision (strictDiagramMappingSpace
        ((F.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget)
        ((G.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget)) :=
  edgewiseDuality (SimplicialCategory.sHom F G) ≫
    edgewiseSubdivisionMap
      (strictDiagramOppositeHom (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget))

/-- 双対後の右端は、元の左端と同じ係数反転の射の合成そのもの。 -/
lemma kanDiagramOppositeHomParameter_right (F G : KanDiagramObject I) :
    kanDiagramOppositeHomParameter F G ≫ edgewiseRight _ =
      edgewiseLeft (SimplicialCategory.sHom F G) ≫
        strictDiagramOppositeHom (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) := by
  rw [kanDiagramOppositeHomParameter, Category.assoc, edgewiseRight_naturality,
    ← Category.assoc, edgewiseDuality_right]

/-- 元の反転豊穣図式の Hom 作用は、左端からの係数反転と厳密に一致する。 -/
lemma kanDiagramUniversalOpposite_mappingSpaceMap (F G : KanDiagramObject I) :
    (kanDiagramUniversalEnriched I).opposite.mappingSpaceMap
        (edgewiseOrdinaryObject F) (edgewiseOrdinaryObject G) =
      edgewiseLeft (SimplicialCategory.sHom F G) ≫
        strictDiagramOppositeHom (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) := by
  apply strictDiagramMappingHom_ext
  intro i
  change edgewiseSubdivisionMap (strictDiagramMappingComponent
      (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i) ≫
        edgewiseOppositeKanEnrichedMap (F.val.obj i).obj (G.val.obj i).obj =
    edgewiseLeft (SimplicialCategory.sHom F G) ≫
      strictDiagramOppositeHom (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) ≫
        strictDiagramMappingComponent _ _ i
  let c := strictDiagramMappingComponent
    (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i
  calc
    _ = edgewiseSubdivisionMap c ≫
        (edgewiseLeft ((ihom (F.val.obj i).obj).obj (G.val.obj i).obj) ≫
          (oppositeInternalHomIso (F.val.obj i).obj (G.val.obj i).obj).hom) := by
      rw [edgewiseOppositeKanEnrichedMap_eq_left]
    _ = (edgewiseSubdivisionMap c ≫ edgewiseLeft _) ≫
        (oppositeInternalHomIso (F.val.obj i).obj (G.val.obj i).obj).hom :=
      (Category.assoc _ _ _).symm
    _ = (edgewiseLeft (SimplicialCategory.sHom F G) ≫ SSet.opFunctor.map c) ≫
        (oppositeInternalHomIso (F.val.obj i).obj (G.val.obj i).obj).hom :=
      congrArg (fun f => f ≫
        (oppositeInternalHomIso (F.val.obj i).obj (G.val.obj i).obj).hom)
        (edgewiseLeft_naturality c)
    _ = _ := by
      have h := congrArg
        (fun f => edgewiseLeft (SimplicialCategory.sHom F G) ≫ f)
        (strictDiagramOppositeHom_component
          (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i).symm
      simp only [Category.assoc] at h ⊢
      convert h using 1 <;> rfl

/-- 反転後の右端は、元の反転豊穣図式の全 Hom 作用を回収する。 -/
lemma kanDiagramOppositeHomParameter_right_action (F G : KanDiagramObject I) :
    kanDiagramOppositeHomParameter F G ≫ edgewiseRight _ =
      (kanDiagramUniversalEnriched I).opposite.mappingSpaceMap
        (edgewiseOrdinaryObject F) (edgewiseOrdinaryObject G) := by
  rw [kanDiagramOppositeHomParameter_right, kanDiagramUniversalOpposite_mappingSpaceMap]

end SerrePositivity.InfinityCategories
