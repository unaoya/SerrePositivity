module

public import SerrePositivity.InfinityCategories.F2.Presentable.CompactFiberCoconeComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactSourceSliceCocones
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleSliceTerminalCocones
public import SerrePositivity.InfinityCategories.F2.Presentable.LeftFibrationCoconeTarget
public import SerrePositivity.InfinityCategories.F2.Presentable.FullSubcomplexEdges
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedShapeCosliceCocone
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedShapeFilteredCriterion
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedPointQuillenA
public import SerrePositivity.InfinityCategories.Stable.Filtered.FilteredWeakContractibility

/-!
概要：点 fiber の compact comma の第一成分射影が right cofinal であることを示す。
方針：指定した始点の下の全余錐を compact な終対象像へ延長し、元の comma へ戻す。
規約：指定始点を含む全図式を保持し、頂点の被覆だけから cofinal 性を推論しない。
使われ方：元の fiber の各対象の compact filtered 生成表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：compact fiber 射影の指定始点の下の小試験図式は全余錐を持つ。
方針：第一成分の coslice で全余錐を延長し、全余錐同型によって元の実引き戻しに貼る。
規約：元の指定始点と試験図式を厳密に保持する。
使われ方：Quillen A へ渡す under comma の filtered 判定。 -/
lemma nonempty_compactFiberProjection_under_cocone
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {K : SSet.{u}} (hK : IsKappaSmall μ K)
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : HasSmallColimits E) (hB : HasSmallColimits B) (hEμ : IsKappaAccessible μ E)
    (p : E ⟶ B) (q : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (hp : F1B.EquivalenceLifting p) (hpc : PreservesSmallColimits p)
    (hpCompact : ∀ e, Compact.IsKappaCompact.{u, u + 1} μ e →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app _ e))
    (hq : Compact.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv q))
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[0] : SSet.{u}) ⟶
      compactSourceSlice μ (x ≫ pullback.fst p q))
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
      pullback (sliceUnderProjection z) (componentCompactOverFst μ p q x)) :
    Nonempty (JoinCocone r) := by
  have : InnerFibration p := hp.innerFibration
  let xe := x ≫ pullback.fst p q
  let Y := compactSourceSlice μ xe
  let P := sliceUnderProjection z
  let F := componentCompactOverFst μ p q x
  let t := r ≫ pullback.fst P F
  let a := r ≫ pullback.snd P F
  have hbase : (a ≫ F) = t ≫ P := by
    dsimp only [a, t]
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hY : ∀ {L : SSet.{u}}, IsKappaSmall μ L →
      ∀ j : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ Y, Nonempty (JoinCocone j) :=
    fun hL j ↦ nonempty_compactSourceSlice_cocone_of_small hμ hL hE xe j
  obtain ⟨cT⟩ := Ind.nonempty_coslice_cocone_liftedShape_of_cocones hY hK
    (isKappaSmall_of_finite hμ.le (Δ[0] : SSet.{u})) z t
  let v := P.app (Opposite.op ⦋0⦌) cT.vertex
  have hxd : x ≫ pullback.snd p q = 𝟙 (Δ[0] : SSet.{u + 1}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hxp : xe ≫ p = q := by
    dsimp only [xe]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hxd, Category.id_comp]
  have hxe : Compact.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv (xe ≫ p)) := by
    rw [hxp]
    exact hq
  obtain ⟨w, hw, htw, ⟨e⟩⟩ := exists_accessibleSliceEdge_image_terminal hμ hE hB hEμ
    p hpc hpCompact xe hxe v.val (fullSubcomplexOnVertices_vertex v)
  let Q := fun b : (sliceOver xe) _⦋0⦌ ↦
    Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection xe).app _ b)
  let wy : Y _⦋0⦌ := ⟨w, by
    intro j
    have hj : j = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hj, op_id, CategoryTheory.Functor.map_id_apply]
    exact hw⟩
  let ey : Y.Edge v wy := fullSubcomplexEdgeLift Q v wy e
  obtain ⟨dT, hdT⟩ := exists_leftFibration_cocone_of_target_edge P cT ey
  let ce : JoinCocone (a ≫ F) := ⟨dT.val ≫ P, by
    rw [← Category.assoc, dT.property]
    exact hbase.symm⟩
  have hce : ce.vertex = wy := by
    change (mapJoinCocone P dT).vertex = wy
    rw [Ind.mapJoinCocone_vertex]
    exact hdT
  have hte : IsTerminalVertex ((sliceOverPostcomp xe p).app (Opposite.op ⦋0⦌) ce.vertex.val) := by
    rw [hce]
    exact htw
  obtain ⟨c, ⟨hc⟩⟩ := exists_compactFiberCocone_with_firstComparison hμ.le hB p q hp x a ce hte
  let e' : VertexIso (X := sliceUnder ((r ≫ pullback.fst P F) ≫ P))
      ((pullbackCoconeBaseMap P F r).app (Opposite.op ⦋0⦌) c)
      (mapJoinCocone P dT) :=
    coconeVertexIso_transport_values hbase
      (pullbackCoconeBaseMap_val P F r c).symm rfl hc
  obtain ⟨d, _, _⟩ := exists_pullbackCocone_of_compatible_components P F
    (leftFibration_equivalenceLifting P) r dT c e'
  exact ⟨d⟩

/-- 概要：compact fiber comma の第一成分射影は right cofinal。
方針：各指定始点の under comma の全小試験余錐から filtered 性と弱可縮性を得る。
規約：元の全射影そのものについて主張する。
使われ方：元の fiber の compact 生成表示の余極限性。 -/
lemma componentCompactFiberOverFst_isRightCofinal
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : HasSmallColimits E) (hB : HasSmallColimits B) (hEμ : IsKappaAccessible μ E)
    (p : E ⟶ B) (q : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (hp : F1B.EquivalenceLifting p) (hpc : PreservesSmallColimits p)
    (hpCompact : ∀ e, Compact.IsKappaCompact.{u, u + 1} μ e →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app _ e))
    (hq : Compact.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv q))
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) :
    letI := hp.innerFibration
    IsRightCofinal (componentCompactOverFst μ p q x) := by
  have : InnerFibration p := hp.innerFibration
  apply Ind.isRightCofinal_of_weaklyContractible_lifted_point_under
  intro z
  have hfiltered := Ind.isFilteredInfinity_of_liftedShape_cocones (Fact.out : μ.IsRegular)
    (pullback (sliceUnderProjection z) (componentCompactOverFst μ p q x))
    (fun hK r ↦ nonempty_compactFiberProjection_under_cocone hμ hK hE hB hEμ
      p q hp hpc hpCompact hq x z r)
  exact isWeaklyContractible_of_isFilteredInfinity _

end SerrePositivity.InfinityCategories.F2.Presentable
