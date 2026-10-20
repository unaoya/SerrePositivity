module

public import SerrePositivity.InfinityCategories.F1.KanDiagramOppositeHomParameter
public import SerrePositivity.InfinityCategories.F1.KanEnrichedHomIntervalNaturality
public import SerrePositivity.InfinityCategories.F1.KanEnrichedTwoSidedHomInterval
public import SerrePositivity.InfinityCategories.F1.OppositeUnstraighteningHomFamilies

/-!
概要：元の反転 coherent 区間族を、同じ全 Hom 上の native な左区間族と比較する。
方針：係数反転の共通パラメーターを左右区間比較へ入れ、右端を元の作用へ戻す。
規約：始域の変換空間の Kan 性も、豊穣作用の代わりとなる選択も用いない。
使われ方：実際の unstraightening 写像空間比較への後合成と、分類写像の作用の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {I : Type u} [SmallCategory I]

/-- 元の反転区間族は、反転図式値の実際の豊穣 Hom 作用に続く標準右区間族。 -/
lemma kanDiagramOppositeHomInterval_eq_action (F G : KanDiagramObject I) :
    kanDiagramOppositeHomInterval F G =
      (SSet.uliftFunctor.{u + 1, u}).map
        ((kanDiagramUniversalEnriched I).opposite.mappingSpaceMap
          (edgewiseOrdinaryObject F) (edgewiseOrdinaryObject G)) ≫
      kanEnrichedDiagramHomInterval (kanDiagramUniversalEnriched I)
        (show KanDiagramObject I from ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
        (show KanDiagramObject I from ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩) rfl rfl := by
  convert kanEnrichedDiagramHomInterval_toEnrichedFunctor
    (kanDiagramUniversalEnriched I).opposite
    (edgewiseOrdinaryObject F) (edgewiseOrdinaryObject G) using 1 <;> rfl

/-- 反転後の共通 Hom の右端は、既存の反転区間族そのものを回収する。 -/
lemma kanDiagramOppositeHomParameter_right_interval (F G : KanDiagramObject I) :
    (SSet.uliftFunctor.{u + 1, u}).map (kanDiagramOppositeHomParameter F G) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight _) ≫
        kanEnrichedDiagramHomInterval (kanDiagramUniversalEnriched I)
          (show KanDiagramObject I from ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
          (show KanDiagramObject I from ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩) rfl rfl =
      kanDiagramOppositeHomInterval F G := by
  rw [← Category.assoc, ← Functor.map_comp,
    kanDiagramOppositeHomParameter_right_action, ← kanDiagramOppositeHomInterval_eq_action]

/-- 同じ元の全 Hom の解像を用い、反転した二図式の native な左区間族を作る。 -/
def kanDiagramOppositeLeftHomInterval (F G : KanDiagramObject I) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (edgewiseSubdivision (SimplicialCategory.sHom F G)) ⟶
    leftUnstraighteningTransformationSpace
      (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
      (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)) :=
  (SSet.uliftFunctor.{u + 1, u}).map (kanDiagramOppositeHomParameter F G) ≫
    (SSet.uliftFunctor.{u + 1, u}).map (edgewiseLeft _) ≫
      kanEnrichedDiagramLeftHomInterval (kanDiagramUniversalEnriched I)
        (show KanDiagramObject I from ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
        (show KanDiagramObject I from ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩) rfl rfl

/-- 全 Hom を保った native な左区間族と、元の反転 coherent 区間族の関手同型。 -/
def kanDiagramOppositeHomIntervalIso (F G : KanDiagramObject I) :
    FunctorIso (kanDiagramOppositeLeftHomInterval F G) (kanDiagramOppositeHomInterval F G) := by
  have e := (kanEnrichedDiagramTwoSidedHomIntervalIso (kanDiagramUniversalEnriched I)
    (show KanDiagramObject I from ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
    (show KanDiagramObject I from ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩) rfl rfl).precomp
      ((SSet.uliftFunctor.{u + 1, u}).map (kanDiagramOppositeHomParameter F G))
  exact e ≪≫ eqToIso (congrArg
    (fun k => SSet.HomotopyCategory.mk (functorVertex k))
    (kanDiagramOppositeHomParameter_right_interval F G))

/-- 左区間族への変更後も、同じ実際の unstraightening 作用の全相対 Hom を回収する。 -/
def oppositeUnstraighteningHomRight_nativeIso (F G : KanDiagramObject I) :
    FunctorIso
      (kanDiagramOppositeLeftHomInterval F G ≫
        leftUnstraighteningMappingSpaceMap
          (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
          (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)) ≫
        relativeFunctorOverPre
          (leftUnstraighteningProjection (kanDiagramCoherentNerve
            (G.val ⋙ kanObjectOpFunctor))) (oppositeKanUnstraighteningOverMap F))
      (oppositeUnstraighteningHomRight F G) :=
  (kanDiagramOppositeHomIntervalIso F G).postcomp
    (leftUnstraighteningMappingSpaceMap
      (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
      (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)) ≫
      relativeFunctorOverPre
        (leftUnstraighteningProjection (kanDiagramCoherentNerve
          (G.val ⋙ kanObjectOpFunctor))) (oppositeKanUnstraighteningOverMap F))

end SerrePositivity.InfinityCategories
