module
public import SerrePositivity.InfinityCategories.Derived.SuspensionSquareHomProjection
public import SerrePositivity.InfinityCategories.Derived.FullInclusionHomotopyObjects
public import SerrePositivity.InfinityCategories.Derived.ChainMapEdge
public import SerrePositivity.InfinityCategories.Stable.ArrowFaithfulReflection
public import SerrePositivity.InfinityCategories.Stable.SquareEvaluationPostcomposition

/-! # Semifree の suspension 四角形比較の両端成分

概要：持ち上げた比較の始点は元の鎖写像、終点は標準 cone 写像の h の類である。
方針：包含後の成分を計算し、対象での単射性と h 上の忠実性で Arrow 等式を反映する。
規約：実際の四角形比較射を用いる。使われ方：D7 の suspension の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {S : Type u} [CommRing S] {X Y : Semifree S}

/-- Semifree の比較の始点成分は元の鎖写像の類。 -/
lemma semifreeSuspensionSquareHom_source_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((squareDiagramHoEvaluation (derivedInfinityCategory S) 0 0).map
      (semifreeSuspensionSquareHom a)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (derivedChainMapEdge (x := Simplex.vertex X) (y := Simplex.vertex Y) a)) := by
  let : (hoFunctor.map (derivedInfinityInclusion (S := S))).toFunctor.Faithful :=
    fullInclusionHo_faithful S (Complex S) (complexSemifree S)
  apply arrowMk_eq_of_faithful_map
    (hoFunctor.map derivedInfinityInclusion).toFunctor
    (fullInclusionHo_obj_injective S (Complex S) (complexSemifree S))
  calc
    _ = Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).map
        ((hoFunctor.map ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
          derivedInfinityInclusion)).toFunctor.map (semifreeSuspensionSquareHom a))) :=
      (squareDiagramHoEvaluation_postcomp_arrow derivedInfinityInclusion
        (semifreeSuspensionSquareHom a) 0 0).symm
    _ = Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).map
        (suspensionComplexSquareHomOnInclusion a)) :=
      congrArg (squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).mapArrow.obj
        (semifreeSuspensionSquareHom_inclusion_arrow a)
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (complexEdge a).toTruncated) :=
      suspensionComplexSquareHomOnInclusion_source_arrow a
    _ = _ := by
      symm
      apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      exact derivedChainMapEdge_inclusion (x := Simplex.vertex X) (y := Simplex.vertex Y) a

/-- Semifree の比較の終点成分は標準 cone 写像の類。 -/
lemma semifreeSuspensionSquareHom_target_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((squareDiagramHoEvaluation (derivedInfinityCategory S) 1 1).map
      (semifreeSuspensionSquareHom a)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (derivedChainMapEdge (x := Simplex.vertex (semifreeSuspensionObject X))
          (y := Simplex.vertex (semifreeSuspensionObject Y))
          (semifreeSuspensionComplexMap a))) := by
  let : (hoFunctor.map (derivedInfinityInclusion (S := S))).toFunctor.Faithful :=
    fullInclusionHo_faithful S (Complex S) (complexSemifree S)
  apply arrowMk_eq_of_faithful_map
    (hoFunctor.map derivedInfinityInclusion).toFunctor
    (fullInclusionHo_obj_injective S (Complex S) (complexSemifree S))
  calc
    _ = Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1).map
        ((hoFunctor.map ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
          derivedInfinityInclusion)).toFunctor.map (semifreeSuspensionSquareHom a))) :=
      (squareDiagramHoEvaluation_postcomp_arrow derivedInfinityInclusion
        (semifreeSuspensionSquareHom a) 1 1).symm
    _ = Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1).map
        (suspensionComplexSquareHomOnInclusion a)) :=
      congrArg (squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1).mapArrow.obj
        (semifreeSuspensionSquareHom_inclusion_arrow a)
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (complexEdge (semifreeSuspensionComplexMap a)).toTruncated) :=
      suspensionComplexSquareHomOnInclusion_target_arrow a
    _ = _ := by
      symm
      apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      exact derivedChainMapEdge_inclusion
        (x := Simplex.vertex (semifreeSuspensionObject X))
        (y := Simplex.vertex (semifreeSuspensionObject Y)) (semifreeSuspensionComplexMap a)

end SerrePositivity.InfinityCategories
