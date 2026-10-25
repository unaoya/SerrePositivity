module

public import SerrePositivity.InfinityCategories.F2.Presentable.NativeAlternatingPresentation
public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeSliceImagePreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.SequentialCompactPullbackVertex
public import SerrePositivity.InfinityCategories.F2.Presentable.PointAccessibility

/-!
概要：元の対象上の可算交互構成から、像が恒等錐と同型な compact 始域の射を構成する。
方針：全交互比較を具体的に構成し、偶数・奇数の共終部分列の余極限を比較する。
規約：第一脚の全小余極限保存だけを使い、交互比較や生成性を入力に仮定しない。
使われ方：元の fiber の対象への compact 始域の射の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

private lemma nativeSequential_isWeaklyContractible :
    IsWeaklyContractible ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ))) := by
  have : Fact Cardinal.aleph0.{u}.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  have : IsCardinalFiltered (ULift.{u} ℕ) Cardinal.aleph0 :=
    (isCardinalFiltered_aleph0_iff _).mpr inferInstance
  have : IsKappaFiltered Cardinal.aleph0 (nerve (ULift.{u} ℕ)) :=
    Ind.isKappaFiltered_nerve_of_cardinalFiltered _
  have : IsFilteredInfinity (nerve (ULift.{u} ℕ)) :=
    isFilteredInfinity_of_isKappaFiltered (le_refl Cardinal.aleph0) _
  have := Compact.isFilteredInfinity_ulift.{u, u + 1} (nerve (ULift.{u} ℕ))
  exact isWeaklyContractible_of_isFilteredInfinity _

/-- 概要：元の compact filtered 表示から、像が恒等錐と同型な compact 始域の実際の射を得る。
方針：元の対象上の全可算交互図式を構成し、その第一成分の可算余極限を取る。
規約：第二脚の小余極限保存も、全交互比較の追加入力も要求しない。
使われ方：固定標的 fiber の元の対象への compact 射の構成。 -/
lemma exists_compactSliceSource_image_identity_initial_of_filteredPresentation
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : HasSmallColimits E) (hB : HasSmallColimits B)
    (p : E ⟶ B) (hp : PreservesSmallColimits p)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ E)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD : ∀ j : I _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up j)))
    (hpD : ∀ j : I _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ ((D ≫ p).app _ (ULift.up j)))
    (hv : Compact.IsKappaCompact.{u, u + 1} μ (mapJoinCocone p c).vertex)
    (i : I _⦋0⦌) :
    ∃ v : (sliceOver (SSet.yonedaEquiv.symm c.vertex)) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)).app (Opposite.op ⦋0⦌) v) ∧
      Nonempty (VertexIso ((coconeSliceImageMap c p).app (Opposite.op ⦋0⦌) v)
        (sliceIdentityCone (mapJoinCocone p c).vertex)) ∧
      Nonempty ((sliceOver (SSet.yonedaEquiv.symm c.vertex)).Edge
        ((coconeSliceDiagram c).app (Opposite.op ⦋0⦌) (ULift.up i)) v) := by
  obtain ⟨J, F, hJ, heven, ⟨hodd⟩⟩ := exists_nativeAlternatingPresentation hμ (D ≫ p)
    (mapJoinCocone p c) (hp I D c hc) hpD hv i
  let FE := (SSet.uliftFunctor.{u + 1, u}).map J ≫ coconeSliceDiagram c
  let P := coconeSliceImageMap c p
  let Y := sliceOver (SSet.yonedaEquiv.symm (mapJoinCocone p c).vertex)
  let t : Y _⦋0⦌ := sliceIdentityCone (mapJoinCocone p c).vertex
  let FD := (SSet.const t : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ Y)
  have heven' : FE ≫ P = (SSet.uliftFunctor.{u + 1, u}).map (nerveMap
      (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) alternatingEven_monotone)) ≫ F := by
    dsimp only [FE, P]
    rw [Category.assoc, coconeSliceDiagram_postcomp]
    exact heven
  let eE : FunctorIso (FE ≫ P) ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap
      (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) alternatingEven_monotone)) ≫ F) :=
    eqToIso (congrArg (fun f ↦ SSet.HomotopyCategory.mk (functorVertex f)) heven')
  have eD : FunctorIso (FD ≫ 𝟙 Y) ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap
      (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n + 1) alternatingOdd_monotone)) ≫ F) := by
    simpa only [Category.comp_id] using hodd.symm
  obtain ⟨cE, hcE⟩ := sliceOver_hasSmallColimits hE (SSet.yonedaEquiv.symm c.vertex)
    (nerve (ULift.{u} ℕ)) FE
  let cD := constantJoinCocone ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ))) t
  have hcD : IsColimitCone cD := constantJoinCocone_isColimit nativeSequential_isWeaklyContractible t
  have hPY := coconeSliceImageMap_preservesSmallColimits c hE p hp
  have hId : PreservesSmallColimits (𝟙 Y) :=
    equivalence_preservesSmallColimits (qCatEquivalenceOfIso (Iso.refl Y)).isQCatEquivalence
  obtain ⟨e⟩ := nonempty_subsequencePreservedImageColimitIso
    (fun n ↦ 2 * n) (fun n ↦ 2 * n + 1) alternatingEven_monotone alternatingOdd_monotone
    (fun k ↦ ⟨k, by omega⟩) (fun k ↦ ⟨k, by omega⟩)
    (sliceOver_hasSmallColimits hB _) P (𝟙 Y) eE eD
    cE (hPY _ FE cE hcE) cD (hId _ FD cD hcD)
  have hd : cD.vertex = t := by
    rw [JoinCocone.vertex_eq]
    change SSet.yonedaEquiv (joinInr _ Δ[0] ≫ SSet.const t) = t
    rw [SSet.comp_const, SSet.yonedaEquiv_const]
  change VertexIso (P.app (Opposite.op ⦋0⦌) cE.vertex) cD.vertex at e
  rw [hd] at e
  have hNat : HasCardinalLT (ULift.{u} ℕ) μ := by
    rw [hasCardinalLT_iff_cardinal_mk_lt]
    simpa only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0] using hμ
  have hFE : ∀ k, Compact.IsKappaCompact.{u, u + 1} μ
      ((FE ≫ sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)).app (Opposite.op ⦋0⦌) k) := by
    have hproj : FE ≫ sliceOverProjection (SSet.yonedaEquiv.symm c.vertex) =
        (SSet.uliftFunctor.{u + 1, u}).map J ≫ D := by
      dsimp only [FE]
      rw [Category.assoc, coconeSliceDiagram_projection]
    intro k
    rw [hproj]
    exact hD (((SSet.uliftFunctor.{u + 1, u}).map J).app (Opposite.op ⦋0⦌) k).down
  have hcompact := isKappaCompact_smallPosetColimit_universe hμ (ULift.{u} ℕ) hNat
    (mapJoinCocone (sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)) cE)
    (sliceOverProjection_preservesSmallColimits hE _ _ FE cE hcE) hFE
  have hcompact' : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)).app (Opposite.op ⦋0⦌) cE.vertex) := by
    simpa only [Ind.mapJoinCocone_vertex] using hcompact
  let k₀ := SSet.yonedaEquiv (nativeSequentialInitialSimplex.{u} 0)
  have hJ₀ : ((SSet.uliftFunctor.{u + 1, u}).map J).app (Opposite.op ⦋0⦌) k₀ =
      ULift.up i := by
    have h := congrArg SSet.yonedaEquiv (nativeSequentialInitialSimplex_liftedDiagram J 0)
    rw [SSet.yonedaEquiv_comp, hJ 0] at h
    change ((SSet.uliftFunctor.{u + 1, u}).map J).app (Opposite.op ⦋0⦌) k₀ =
      SSet.yonedaEquiv (finiteStageBaseMap (SSet.yonedaEquiv.symm i)) at h
    dsimp only [finiteStageBaseMap] at h
    rw [uliftYonedaMap, Equiv.apply_symm_apply] at h
    exact h
  have hFE₀ : FE.app (Opposite.op ⦋0⦌) k₀ =
      (coconeSliceDiagram c).app (Opposite.op ⦋0⦌) (ULift.up i) := by
    change (coconeSliceDiagram c).app (Opposite.op ⦋0⦌)
      (((SSet.uliftFunctor.{u + 1, u}).map J).app (Opposite.op ⦋0⦌) k₀) = _
    rw [hJ₀]
  have leg := Compact.coconeTransportLeg cE k₀
  rw [hFE₀] at leg
  exact ⟨cE.vertex, hcompact', ⟨e⟩, ⟨leg⟩⟩

/-- 概要：元の compact 表示から像が恒等錐と同型な compact 始域の射を得る。
方針：指定初期段からの全比較を保持する強い入口の射を使う。
規約：既存の公開入口の型を保持する。
使われ方：元の fiber の各対象上の compact 成分の回収。 -/
lemma exists_compactSliceSource_image_identity_of_filteredPresentation
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : HasSmallColimits E) (hB : HasSmallColimits B)
    (p : E ⟶ B) (hp : PreservesSmallColimits p)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ E)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD : ∀ j : I _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up j)))
    (hpD : ∀ j : I _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ ((D ≫ p).app _ (ULift.up j)))
    (hv : Compact.IsKappaCompact.{u, u + 1} μ (mapJoinCocone p c).vertex)
    (i : I _⦋0⦌) :
    ∃ v : (sliceOver (SSet.yonedaEquiv.symm c.vertex)) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)).app (Opposite.op ⦋0⦌) v) ∧
      Nonempty (VertexIso ((coconeSliceImageMap c p).app (Opposite.op ⦋0⦌) v)
        (sliceIdentityCone (mapJoinCocone p c).vertex)) := by
  obtain ⟨v, hv, he, _⟩ := exists_compactSliceSource_image_identity_initial_of_filteredPresentation
    hμ hE hB p hp D c hc hD hpD hv i
  exact ⟨v, hv, he⟩

end SerrePositivity.InfinityCategories.F2.Presentable
