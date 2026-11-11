module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.HomologyCharts
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses
/-!
概要：実ホモロジー余錐の全基点チャートから、橋の元ごとの五条件を導く。
方針：filtered 加群余極限の元の表示と等号の後続段検出を使う。
規約：群余極限を使わず、全基点と指定道を保持する。
使われ方：Dold–Kan の評価チャートを Ind-π の Prop 入力へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory Limits SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {I : Type u} [PartialOrder I] [IsFiltered I]
  {X : I → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w}} {A : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w}}
  {τ : ∀ {i j : I}, i ≤ j → ((X i).obj ⟶ (X j).obj)}
  {l : ∀ i : I, ((X i).obj ⟶ A.obj)}
  (H : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactHomologyCharts R X A τ l)

include H

lemma dgBarCompactPiData_of_homologyCharts : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactSpacePiData X A τ l := by
  constructor
  · intro z
    obtain ⟨i, a, ha⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactHomology_jointly_surjective H 0 (H.zeroApex (π₀.mk z))
    obtain ⟨y, hy⟩ := π₀.mk_surjective ((H.zeroStage i).symm a)
    refine ⟨i, y, H.zeroApex.injective ?_⟩
    rw [H.zero_leg, hy, Equiv.apply_symm_apply, ha]
  · intro i j y z he
    have he' := congrArg H.zeroApex he
    rw [H.zero_leg, H.zero_leg] at he'
    obtain ⟨k, hik, hjk, hk⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactHomology_equal_at_stage H 0 _ _ he'
    refine ⟨k, hik, hjk, (H.zeroStage k).injective ?_⟩
    rw [H.zero_transition, H.zero_transition]
    exact hk
  · intro n i y a
    obtain ⟨j, b, hb⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactHomology_jointly_surjective H (n + 1)
      (H.positiveApex n ((l i).app _ y) a)
    let k := IsFiltered.max i j
    have hik : i ≤ k := leOfHom (IsFiltered.leftToMax i j)
    have hjk : j ≤ k := leOfHom (IsFiltered.rightToMax i j)
    let z := (τ hik).app _ y
    let b' := (H.positiveStage n k z).symm ((H.diagram (n + 1)).map (homOfLE hjk) b)
    refine ⟨k, hik, b', ?_⟩
    intro e
    apply H.transport
    rw [H.positive_leg]
    change (H.cocone (n + 1)).ι.app k
      (H.positiveStage n k z ((H.positiveStage n k z).symm _)) = _
    rw [Equiv.apply_symm_apply]
    exact (ConcreteCategory.congr_hom ((H.cocone (n + 1)).w (homOfLE hjk)) b).trans hb
  · intro n i y a b he
    have he' := congrArg (H.positiveApex n ((l i).app _ y)) he
    rw [H.positive_leg, H.positive_leg] at he'
    obtain ⟨j, hij, hj⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactHomology_equal_at_stage_same H (n + 1) _ _ he'
    refine ⟨j, hij, (H.positiveStage n j ((τ hij).app _ y)).injective ?_⟩
    rw [H.positive_transition, H.positive_transition]
    exact hj
  · intro n z a
    obtain ⟨i, b₀, hb₀⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactHomology_jointly_surjective H 0 (H.zeroApex (π₀.mk z))
    obtain ⟨y, hy⟩ := π₀.mk_surjective ((H.zeroStage i).symm b₀)
    have hy' : H.zeroStage i (π₀.mk y) = b₀ := by rw [hy, Equiv.apply_symm_apply]
    obtain ⟨j, b, hb⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactHomology_jointly_surjective H (n + 1)
      (H.positiveApex n z a)
    let k := IsFiltered.max i j
    have hik : i ≤ k := leOfHom (IsFiltered.leftToMax i j)
    have hjk : j ≤ k := leOfHom (IsFiltered.rightToMax i j)
    let y' := (τ hik).app _ y
    have hpath : π₀.mk ((l k).app _ y') = π₀.mk z := by
      apply H.zeroApex.injective
      rw [H.zero_leg]
      change (H.cocone 0).ι.app k (H.zeroStage k (π₀.mk ((τ hik).app _ y))) = _
      rw [H.zero_transition, hy']
      exact (ConcreteCategory.congr_hom ((H.cocone 0).w (homOfLE hik)) b₀).trans hb₀
    obtain ⟨e₀⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.nonempty_vertexIso_of_piZero_eq hpath
    obtain ⟨e₁, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ e₀.hom
    let e : A.obj.Edge ((l k).app _ y') z := SSet.Edge.ofTruncated e₁
    let b' := (H.positiveStage n k y').symm ((H.diagram (n + 1)).map (homOfLE hjk) b)
    refine ⟨k, y', b', e, H.transport n e _ a ?_⟩
    rw [H.positive_leg]
    change (H.cocone (n + 1)).ι.app k
      (H.positiveStage n k y' ((H.positiveStage n k y').symm _)) = _
    rw [Equiv.apply_symm_apply]
    exact (ConcreteCategory.congr_hom ((H.cocone (n + 1)).w (homOfLE hjk)) b).trans hb

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
