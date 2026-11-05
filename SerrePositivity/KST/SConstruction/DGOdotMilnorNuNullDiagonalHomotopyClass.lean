module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullDiagonalIntervalClass
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFunctorHom
/-!
概要：元上下全三角形の対角ホモトピーは元の関手圏で同じ射の類を持つ。
方針：実両端固定区間 Hom の同じ類を元内部 Hom へ写し、端点を厳密回収する。
規約：元実／絶対両対角辺を保持し、三角形の二胞体を変更しない。
使われ方：元全三角形比較の類を保つ対角代表修正。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : DGGluingMilnorSquare R d)
/-- 概要：元上下共有対角の全ホモトピーの辺は同じ元関手圏で同じ射を表す。
方針：両端固定区間の一意性を忘却射で運び、元対角辺の回収で端点を合わせる。
規約：元の二つの実全一単体。使われ方：全三角形比較を保つ厳密な共有対角。 -/
lemma dgOdotMilnorNuNullDiagonalHomotopy_homMk_eq :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgOdotMilnorNuNullLowerDiagonalHomotopy R d h)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h)) := by
  let p := vertexFiberι ((pre (boundary 1 : (Δ[1] : SSet.{u + 2}).Subcomplex).ι).app
      _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u + 1}) (functorVertex (intervalMappingBoundary
        (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex (dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)))
        (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)))))
  have hx : p.app (Opposite.op ⦋0⦌)
      (intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (dgOdotMilnorNuNullDiagonalMap R d))) =
      functorVertex (squareDiagonal ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R) := by
    change functorVertex (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (dgOdotMilnorNuNullDiagonalMap R d)).edge) = _
    exact congrArg functorVertex (dgOdotMilnorNuNullDiagonalMap_diagram R d)
  have hy : p.app (Opposite.op ⦋0⦌)
      (intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (dgOdotMilnorNuAbsoluteDiagonalMap R d h))) =
      functorVertex (squareDiagonal ≫
        perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) := by
    change functorVertex (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (dgOdotMilnorNuAbsoluteDiagonalMap R d h)).edge) = _
    exact congrArg functorVertex (dgOdotMilnorNuAbsoluteDiagonalMap_diagram R d h)
  have hl : ((dgOdotMilnorNuNullLowerDiagonalIntervalEdge R d h).toTruncated.map
      ((truncation 2).map p)).edge = (functorEdgeOfSimplicialHomotopy
        (dgOdotMilnorNuNullLowerDiagonalHomotopy R d h)).edge := by
    change p.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (dgOdotMilnorNuNullLowerDiagonalIntervalParameter R d h)) =
        SSet.yonedaEquiv (curry (dgOdotMilnorNuNullLowerDiagonalHomotopy R d h).h)
    apply (SSet.yonedaEquiv_comp
      (dgOdotMilnorNuNullLowerDiagonalIntervalParameter R d h) p).symm.trans
    apply congrArg SSet.yonedaEquiv
    apply uncurry_injective
    change intervalMappingUncurry (dgOdotMilnorNuNullLowerDiagonalIntervalParameter R d h) = _
    rw [dgOdotMilnorNuNullLowerDiagonalIntervalParameter_uncurry, uncurry_curry]
  have hu : ((dgOdotMilnorNuNullUpperDiagonalIntervalEdge R d h).toTruncated.map
      ((truncation 2).map p)).edge = (functorEdgeOfSimplicialHomotopy
        (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h)).edge := by
    change p.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (dgOdotMilnorNuNullUpperDiagonalIntervalParameter R d h)) =
        SSet.yonedaEquiv (curry (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h)
    apply (SSet.yonedaEquiv_comp
      (dgOdotMilnorNuNullUpperDiagonalIntervalParameter R d h) p).symm.trans
    apply congrArg SSet.yonedaEquiv
    apply uncurry_injective
    change intervalMappingUncurry (dgOdotMilnorNuNullUpperDiagonalIntervalParameter R d h) = _
    rw [dgOdotMilnorNuNullUpperDiagonalIntervalParameter_uncurry, uncurry_curry]
  have hh := congrArg ((hoFunctor.map p).toFunctor.map)
    (dgOdotMilnorNuNullDiagonalIntervalEdge_homMk_eq R d h)
  change SSet.Truncated.HomotopyCategory.homMk
      ((dgOdotMilnorNuNullLowerDiagonalIntervalEdge R d h).toTruncated.map ((truncation 2).map p)) =
    SSet.Truncated.HomotopyCategory.homMk
      ((dgOdotMilnorNuNullUpperDiagonalIntervalEdge R d h).toTruncated.map
        ((truncation 2).map p)) at hh
  rw [← homMk_transport hx hy _ _ hl, ← homMk_transport hx hy _ _ hu]
  exact congrArg (fun q => eqToHom (congrArg SSet.HomotopyCategory.mk hx).symm ≫ q ≫
    eqToHom (congrArg SSet.HomotopyCategory.mk hy)) hh
end SerrePositivity.KST.SConstruction
