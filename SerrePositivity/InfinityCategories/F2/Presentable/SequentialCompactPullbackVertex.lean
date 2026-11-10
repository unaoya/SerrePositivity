module

public import SerrePositivity.InfinityCategories.F2.Presentable.SequentialImageColimitComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.PullbackSliceVertexCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.SliceOverSmallColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPosetColimitCompactUniverse

/-!
概要：元の対象上の可算交互比較から、compact 成分を持つ引き戻し内の実際の射を回収する。
方針：指定した余極限の像だけを比較し、slice 射影と可算余極限の compact 閉性を使う。
規約：両脚の全小余極限保存を仮定せず、元の対象上の全図式比較を要求する。
使われ方：点射を第二脚とする fiber の可算交互構成の終段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：指定余極限の像が余極限なら、共通の可算列の共終部分列比較で像の頂点が同型。
方針：指定した像の全余錐を関手同型で輸送して、同じ全列で比較する。
規約：関手の全形状の保存性は不要。
使われ方：filtered 形状だけを保存する点射との比較。 -/
lemma nonempty_subsequencePreservedImageColimitIso
    (a b : ℕ → ℕ) (ha : Monotone a) (hb : Monotone b)
    (hca : ∀ k, ∃ n, k ≤ a n) (hcb : ∀ k, ∃ n, k ≤ b n)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits B) (p : E ⟶ B) (q : D ⟶ B)
    {FE : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ E}
    {FD : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ D}
    {F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ B}
    (eE : FunctorIso (FE ≫ p) ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (sequentialSubsequenceFunctor.{u} a ha)) ≫ F))
    (eD : FunctorIso (FD ≫ q) ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (sequentialSubsequenceFunctor.{u} b hb)) ≫ F))
    (cE : JoinCocone FE) (hcE : IsColimitCone (mapJoinCocone p cE))
    (cD : JoinCocone FD) (hcD : IsColimitCone (mapJoinCocone q cD)) :
    Nonempty (VertexIso (p.app (Opposite.op ⦋0⦌) cE.vertex)
      (q.app (Opposite.op ⦋0⦌) cD.vertex)) := by
  let dE := colimitCoconeOfFunctorIso eE (mapJoinCocone p cE) hcE
  let dD := colimitCoconeOfFunctorIso eD (mapJoinCocone q cD) hcD
  obtain ⟨e⟩ := nonempty_subsequenceColimitVertexIso a b ha hb hca hcb hB
    dE (colimitCoconeOfFunctorIso_isColimit _ _ _)
    dD (colimitCoconeOfFunctorIso_isColimit _ _ _)
  exact ⟨by simpa only [dE, dD, colimitCoconeOfFunctorIso_vertex,
    Ind.mapJoinCocone_vertex] using e⟩

/-- 概要：対象上の可算交互比較の余極限は、compact 成分の引き戻し頂点を与える。
方針：各成分の底の可算余極限を compact と判定し、同じ slice 内の像の同型を貼る。
規約：指定した二つの可算余極限の像の普遍性だけを入力にする。
使われ方：fiber の交互構成を元の対象への実際の射へ接続する。 -/
lemma exists_componentCompactOverVertex_of_sequential_comparison
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    (a b : ℕ → ℕ) (ha : Monotone a) (hb : Monotone b)
    (hca : ∀ k, ∃ n, k ≤ a n) (hcb : ∀ k, ∃ n, k ≤ b n)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D) (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits B)
    (p : E ⟶ B) (q : D ⟶ B) (hp : F1B.EquivalenceLifting p)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    {FE : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
      sliceOver (x ≫ pullback.fst p q)}
    {FD : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
      sliceOver (x ≫ pullback.snd p q)}
    {F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
      sliceOver ((x ≫ pullback.fst p q) ≫ p)}
    (eE : FunctorIso (FE ≫ sliceOverPostcomp (x ≫ pullback.fst p q) p)
      ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (sequentialSubsequenceFunctor.{u} a ha)) ≫ F))
    (eD : FunctorIso (FD ≫ pullbackSliceBaseMap p q x)
      ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (sequentialSubsequenceFunctor.{u} b hb)) ≫ F))
    (cE : JoinCocone FE) (hcE : IsColimitCone cE)
    (cD : JoinCocone FD) (hcD : IsColimitCone cD)
    (hpE : IsColimitCone (mapJoinCocone (sliceOverPostcomp (x ≫ pullback.fst p q) p) cE))
    (hqD : IsColimitCone (mapJoinCocone (pullbackSliceBaseMap p q x) cD))
    (hFE : ∀ k, Compact.IsKappaCompact.{u, u + 1} μ
      ((FE ≫ sliceOverProjection (x ≫ pullback.fst p q)).app (Opposite.op ⦋0⦌) k))
    (hFD : ∀ k, Compact.IsKappaCompact.{u, u + 1} μ
      ((FD ≫ sliceOverProjection (x ≫ pullback.snd p q)).app (Opposite.op ⦋0⦌) k)) :
    ∃ v : (sliceOver x) _⦋0⦌,
      ComponentCompactVertex μ p q ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v) := by
  have hNat : HasCardinalLT (ULift.{u} ℕ) μ := by
    rw [hasCardinalLT_iff_cardinal_mk_lt]
    simpa only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0] using hμ
  have hcompactE := isKappaCompact_smallPosetColimit_universe hμ (ULift.{u} ℕ) hNat
    (mapJoinCocone (sliceOverProjection (x ≫ pullback.fst p q)) cE)
    (sliceOverProjection_preservesSmallColimits hE _ _ _ cE hcE) hFE
  have hcompactD := isKappaCompact_smallPosetColimit_universe hμ (ULift.{u} ℕ) hNat
    (mapJoinCocone (sliceOverProjection (x ≫ pullback.snd p q)) cD)
    (sliceOverProjection_preservesSmallColimits hD _ _ _ cD hcD) hFD
  obtain ⟨e⟩ := nonempty_subsequencePreservedImageColimitIso a b ha hb hca hcb
    (sliceOver_hasSmallColimits hB _) _ _ eE eD cE hpE cD hqD
  exact exists_componentCompactOverVertex_of_compatible_sources p q hp x
    cE.vertex cD.vertex e.symm hcompactE hcompactD

end SerrePositivity.InfinityCategories.F2.Presentable
