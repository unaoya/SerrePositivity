module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SuspensionSquareHomProjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullInclusionHomotopyObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ChainMapEdge
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ArrowFaithfulReflection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareEvaluationPostcomposition

/-! # Semifree の suspension 四角形比較の両端成分

概要：持ち上げた比較の始点は元の鎖写像、終点は標準 cone 写像の h の類である。
方針：包含後の成分を計算し、対象での単射性と h 上の忠実性で Arrow 等式を反映する。
規約：実際の四角形比較射を用いる。使われ方：D7 の suspension の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- Semifree の比較の始点成分は元の鎖写像の類。 -/
lemma semifreeSuspensionSquareHom_source_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) 0 0).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom a)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a)) := by
  let : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := S))).toFunctor.Faithful :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionHo_faithful S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_eq_of_faithful_map
    (hoFunctor.map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion).toFunctor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionHo_obj_injective S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S))
  calc
    _ = Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).map
        ((hoFunctor.map ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom a))) :=
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation_postcomp_arrow _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom a) 0 0).symm
    _ = Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHomOnInclusion a)) :=
      congrArg (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).mapArrow.obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom_inclusion_arrow a)
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge a).toTruncated) :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHomOnInclusion_source_arrow a
    _ = _ := by
      symm
      apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_inclusion (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a

/-- Semifree の比較の終点成分は標準 cone 写像の類。 -/
lemma semifreeSuspensionSquareHom_target_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) 1 1).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom a)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X))
          (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject Y))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a))) := by
  let : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := S))).toFunctor.Faithful :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionHo_faithful S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_eq_of_faithful_map
    (hoFunctor.map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion).toFunctor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionHo_obj_injective S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S))
  calc
    _ = Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 1 1).map
        ((hoFunctor.map ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom a))) :=
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation_postcomp_arrow _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom a) 1 1).symm
    _ = Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 1 1).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHomOnInclusion a)) :=
      congrArg (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 1 1).mapArrow.obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom_inclusion_arrow a)
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a)).toTruncated) :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHomOnInclusion_target_arrow a
    _ = _ := by
      symm
      apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_inclusion
        (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X))
        (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject Y)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
