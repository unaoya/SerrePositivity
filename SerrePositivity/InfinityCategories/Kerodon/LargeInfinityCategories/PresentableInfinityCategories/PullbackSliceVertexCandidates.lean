module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackSliceComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SlicePostcompEquivalenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackVertexCandidates
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactPullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceProjectionLaws

/-!
概要：元の対象上で互いに整合する成分の射を、引き戻し内の同じ対象への射に貼る。
方針：全 slice 比較と slice の同値持ち上げを使う。
規約：底の同型は元の対象上の slice 内で要求する。
使われ方：compact 成分の同期結果を元の comma の実際の頂点に戻す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：対象上で整合する二つの成分射は元の引き戻しの対象上の射を定める。
方針：slice の同値持ち上げで整合を厳密化し、全 slice 同型で戻す。
規約：第一成分は同じ slice 内で同型、第二成分は元の射そのもの。
使われ方：元の対象への全増大図式を保つ同期。 -/
lemma exists_pullbackSliceVertex_of_compatible_components
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    (cE : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (x ≫ pullback.fst p q)) _⦋0⦌)
    (cD : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (x ≫ pullback.snd p q)) _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackSliceBaseMap p q x).app (Opposite.op ⦋0⦌) cD)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (x ≫ pullback.fst p q) p).app (Opposite.op ⦋0⦌) cE)) :
    ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x) _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x (pullback.fst p q)).app
        (Opposite.op ⦋0⦌) v) cE) ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x (pullback.snd p q)).app (Opposite.op ⦋0⦌) v = cD := by
  let pe := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (x ≫ pullback.fst p q) p
  let qd := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackSliceBaseMap p q x
  have hpe : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting pe :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.sliceOverPostcomp_equivalenceLifting (x ≫ pullback.fst p q) p hp
  let w := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackVertexCandidate pe qd hpe cE cD e
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackSliceIso p q x
  have hf : s.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x (pullback.fst p q) = pullback.fst pe qd := by
    dsimp only [s, pe, qd]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackSliceIso_hom_fst p q x, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hd : s.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x (pullback.snd p q) = pullback.snd pe qd := by
    dsimp only [s, pe, qd]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackSliceIso_hom_snd p q x, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨s.inv.app (Opposite.op ⦋0⦌) w.vertex, ?_, ?_⟩
  · have he := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) w.vertex) hf
    change Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((s.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x (pullback.fst p q)).app
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
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    (cE : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (x ≫ pullback.fst p q)) _⦋0⦌)
    (cD : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (x ≫ pullback.snd p q)) _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackSliceBaseMap p q x).app (Opposite.op ⦋0⦌) cD)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (x ≫ pullback.fst p q) p).app (Opposite.op ⦋0⦌) cE))
    (hcE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (x ≫ pullback.fst p q)).app (Opposite.op ⦋0⦌) cE))
    (hcD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (x ≫ pullback.snd p q)).app (Opposite.op ⦋0⦌) cD)) :
    ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨v, ⟨he⟩, hd⟩ := exists_pullbackSliceVertex_of_compatible_components p q hp x cE cD e
  have hfst := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection x (pullback.fst p q))
  have hsnd := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection x (pullback.snd p q))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (x ≫ pullback.fst p q)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x (pullback.fst p q)).app (Opposite.op ⦋0⦌) v) =
    (pullback.fst p q).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) v) at hfst
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (x ≫ pullback.snd p q)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x (pullback.snd p q)).app (Opposite.op ⦋0⦌) v) =
    (pullback.snd p q).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) v) at hsnd
  have he' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map he (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (x ≫ pullback.fst p q))
  rw [hfst] at he'
  refine ⟨v, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso he').mpr hcE, ?_⟩
  rw [← hsnd, hd]
  exact hcD

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
