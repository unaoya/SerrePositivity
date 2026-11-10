module

public import SerrePositivity.InfinityCategories.F2.Presentable.CompactSourceSliceDensity
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactFiberProjectionCofinal
public import SerrePositivity.InfinityCategories.F2.Presentable.PointFiberFilteredColimits

/-!
概要：元の点 fiber の各対象を compact 両成分の小さい filtered 全表示で表す。
方針：compact comma の小模型を標準全余錐へ送り、第一成分の密度と cofinal 性で余極限を判定する。
規約：元の対象を指定頂点として保持し、点射の全小余極限保存を使わない。
使われ方：点 fiber の accessibility の生成性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の点 fiber の各対象は compact 両成分の小さい μ-filtered 全表示を持つ。
方針：compact comma の小さい全同値模型上で元の標準余錐を取り、両成分で余極限性を判定する。
規約：元の対象の頂点を厳密に回収する。
使われ方：小さい compact 生成模型による fiber accessibility。 -/
lemma exists_componentCompactFiberPresentation
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E) (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits B)
    (hEμ : IsKappaAccessible μ E) (hBμ : IsKappaAccessible μ B)
    (p : E ⟶ B) (q : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (hp : F1B.EquivalenceLifting p) (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p)
    (hpCompact : ∀ e, Compact.IsKappaCompact.{u, u + 1} μ e →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app _ e))
    (hq : Compact.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv q))
    (x : (pullback p q) _⦋0⦌) :
    letI := hp.innerFibration
    ∃ (M : SSet.{u}) (hM : Quasicategory M), letI := hM
      IsKappaFiltered μ M ∧ ∃ D : (SSet.uliftFunctor.{u + 1, u}).obj M ⟶ pullback p q,
        (∀ k, ComponentCompactVertex μ p q (D.app (Opposite.op ⦋0⦌) k)) ∧
        ∃ c : JoinCocone D, IsColimitCone c ∧ c.vertex = x := by
  have : InnerFibration p := hp.innerFibration
  let a := SSet.yonedaEquiv.symm x
  let ae := a ≫ pullback.fst p q
  obtain ⟨M, hM, hfiltered, ⟨e⟩⟩ := exists_smallKappaFilteredFiberCommaModel hμ hE hB hEμ hBμ
    p q hp hpc hpCompact hq a
  have := hM
  have := hfiltered
  let P := fun v : (sliceOver a) _⦋0⦌ ↦
    ComponentCompactVertex μ p q ((sliceOverProjection a).app _ v)
  let j := (fullSubcomplexOnVertices (sliceOver a) P).ι
  let T := e.hom ≫ j
  let D := T ≫ sliceOverProjection a
  let c : JoinCocone D := sliceDiagramCocone T
  have hv : c.vertex = x := by
    apply SSet.yonedaEquiv.symm.injective
    exact sliceDiagramCocone_point T
  have hD : ∀ k, ComponentCompactVertex μ p q (D.app (Opposite.op ⦋0⦌) k) := by
    intro k
    exact fullSubcomplexOnVertices_vertex (e.hom.app (Opposite.op ⦋0⦌) k)
  let F := componentCompactOverFst μ p q a
  let je := (fullSubcomplexOnVertices (sliceOver ae)
    (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection ae).app _ v))).ι
  let ce := compactSourceSliceDensityCocone μ ae
  have hce : IsColimitCone ce := compactSourceSliceDensityCocone_isColimit hEμ hE ae
  have hcR : IsColimitCone (ce.restrict F) :=
    (Ind.isColimitCone_iff_restrict_rightCofinal F
      (componentCompactFiberOverFst_isRightCofinal hμ hE hB hEμ p q hp hpc hpCompact hq a) ce).mp hce
  have hcM : IsColimitCone ((ce.restrict F).restrict e.hom) :=
    (Ind.isColimitCone_iff_restrict_equivalentShape e.hom e.isQCatEquivalence _).mp hcR
  have heval : ((ce.restrict F).restrict e.hom).val =
      (mapJoinCocone (pullback.fst p q) c).val := by
    change joinMap e.hom (𝟙 Δ[0]) ≫
      (joinMap F (𝟙 Δ[0]) ≫ sliceOverUncurry je) = sliceOverUncurry T ≫ pullback.fst p q
    rw [← sliceOverUncurry_precomp, ← sliceOverUncurry_precomp]
    rw [show F ≫ je = j ≫ sliceOverPostcomp a (pullback.fst p q) from
      componentCompactOverFst_inclusion μ p q a]
    rw [← Category.assoc, sliceOverUncurry_postcomp]
  have hcf : IsColimitCone (mapJoinCocone (pullback.fst p q) c) :=
    (F2.isColimitCone_iff_of_cocone_val_eq _ _ heval).mp hcM
  have hc : IsColimitCone c :=
    (pullback_filtered_isColimitCone_iff_components p q hp
      (hE.hasSmallKappaFilteredColimits μ) (point_hasSmallColimits.hasSmallKappaFilteredColimits μ)
      (hpc.isKappaAccessibleFunctor μ) (pointMap_isKappaAccessibleFunctor (Fact.out : μ.IsRegular) q) c).mpr
        ⟨hcf, point_cocone_isColimit _⟩
  exact ⟨M, hM, hfiltered, D, hD, c, hc, hv⟩

end SerrePositivity.InfinityCategories.F2.Presentable
