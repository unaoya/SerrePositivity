module

public import SerrePositivity.InfinityCategories.F2.Presentable.PullbackSliceComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.SlicePostcompEquivalenceLifting
public import SerrePositivity.InfinityCategories.F2.Presentable.PullbackVertexCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.ComponentCompactPullback
public import SerrePositivity.InfinityCategories.F1B.Cones.SliceProjectionLaws

/-!
概要：元の対象上で互いに整合する成分の射を、引き戻し内の同じ対象への射に貼る。
方針：全 slice 比較と slice の同値持ち上げを使う。
規約：底の同型は元の対象上の slice 内で要求する。
使われ方：compact 成分の同期結果を元の comma の実際の頂点に戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：対象上で整合する二つの成分射は元の引き戻しの対象上の射を定める。
方針：slice の同値持ち上げで整合を厳密化し、全 slice 同型で戻す。
規約：第一成分は同じ slice 内で同型、第二成分は元の射そのもの。
使われ方：元の対象への全増大図式を保つ同期。 -/
lemma exists_pullbackSliceVertex_of_compatible_components
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : F1B.EquivalenceLifting p)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    (cE : (sliceOver (x ≫ pullback.fst p q)) _⦋0⦌)
    (cD : (sliceOver (x ≫ pullback.snd p q)) _⦋0⦌)
    (e : VertexIso ((pullbackSliceBaseMap p q x).app (Opposite.op ⦋0⦌) cD)
      ((sliceOverPostcomp (x ≫ pullback.fst p q) p).app (Opposite.op ⦋0⦌) cE)) :
    ∃ v : (sliceOver x) _⦋0⦌,
      Nonempty (VertexIso ((sliceOverPostcomp x (pullback.fst p q)).app
        (Opposite.op ⦋0⦌) v) cE) ∧
      (sliceOverPostcomp x (pullback.snd p q)).app (Opposite.op ⦋0⦌) v = cD := by
  let pe := sliceOverPostcomp (x ≫ pullback.fst p q) p
  let qd := pullbackSliceBaseMap p q x
  have hpe : F1B.EquivalenceLifting pe :=
    sliceOverPostcomp_equivalenceLifting (x ≫ pullback.fst p q) p hp
  let w := pullbackVertexCandidate pe qd hpe cE cD e
  let s := pullbackSliceIso p q x
  have hf : s.inv ≫ sliceOverPostcomp x (pullback.fst p q) = pullback.fst pe qd := by
    dsimp only [s, pe, qd]
    rw [← pullbackSliceIso_hom_fst p q x, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hd : s.inv ≫ sliceOverPostcomp x (pullback.snd p q) = pullback.snd pe qd := by
    dsimp only [s, pe, qd]
    rw [← pullbackSliceIso_hom_snd p q x, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨s.inv.app (Opposite.op ⦋0⦌) w.vertex, ?_, ?_⟩
  · have he := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) w.vertex) hf
    change Nonempty (VertexIso ((s.inv ≫ sliceOverPostcomp x (pullback.fst p q)).app
      (Opposite.op ⦋0⦌) w.vertex) cE)
    rw [he]
    exact ⟨w.fstIso⟩
  · have he := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) w.vertex) hd
    exact he.trans w.snd_eq

/-- 概要：対象上で整合する compact 始域の成分射は compact 成分の元の comma 頂点を与える。
方針：slice 内の成分比較を射影し、compact 性を同型で移す。
規約：底の頂点同型だけに弱めず、元の対象上の比較を使う。
使われ方：交互列からの同期結果を compact 生成添字へ戻す。 -/
lemma exists_componentCompactOverVertex_of_compatible_sources
    {μ : Cardinal.{u}} {E D B : SSet.{u + 1}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : F1B.EquivalenceLifting p)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    (cE : (sliceOver (x ≫ pullback.fst p q)) _⦋0⦌)
    (cD : (sliceOver (x ≫ pullback.snd p q)) _⦋0⦌)
    (e : VertexIso ((pullbackSliceBaseMap p q x).app (Opposite.op ⦋0⦌) cD)
      ((sliceOverPostcomp (x ≫ pullback.fst p q) p).app (Opposite.op ⦋0⦌) cE))
    (hcE : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (x ≫ pullback.fst p q)).app (Opposite.op ⦋0⦌) cE))
    (hcD : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (x ≫ pullback.snd p q)).app (Opposite.op ⦋0⦌) cD)) :
    ∃ v : (sliceOver x) _⦋0⦌,
      ComponentCompactVertex μ p q ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨v, ⟨he⟩, hd⟩ := exists_pullbackSliceVertex_of_compatible_components p q hp x cE cD e
  have hfst := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v)
    (F1B.sliceOverPostcomp_projection x (pullback.fst p q))
  have hsnd := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v)
    (F1B.sliceOverPostcomp_projection x (pullback.snd p q))
  change (sliceOverProjection (x ≫ pullback.fst p q)).app (Opposite.op ⦋0⦌)
      ((sliceOverPostcomp x (pullback.fst p q)).app (Opposite.op ⦋0⦌) v) =
    (pullback.fst p q).app (Opposite.op ⦋0⦌)
      ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v) at hfst
  change (sliceOverProjection (x ≫ pullback.snd p q)).app (Opposite.op ⦋0⦌)
      ((sliceOverPostcomp x (pullback.snd p q)).app (Opposite.op ⦋0⦌) v) =
    (pullback.snd p q).app (Opposite.op ⦋0⦌)
      ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v) at hsnd
  have he' := VertexIso.map he (sliceOverProjection (x ≫ pullback.fst p q))
  rw [hfst] at he'
  refine ⟨v, (Compact.isKappaCompact_iff_of_iso he').mpr hcE, ?_⟩
  rw [← hsnd, hd]
  exact hcD

end SerrePositivity.InfinityCategories.F2.Presentable
