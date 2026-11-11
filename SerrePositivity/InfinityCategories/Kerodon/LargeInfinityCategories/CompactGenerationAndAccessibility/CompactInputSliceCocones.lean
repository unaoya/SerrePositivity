module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.InputCoconeRecovery

/-!
概要：元の accessible な底に対する compact 成分 slice 図式の余錐を構成する。
方針：固定入力付き相対交互構成の比較同型を同値持ち上げで厳密化して貼る。
規約：全小余極限や反射の存在を追加仮定にしない。
使われ方：一般 accessible 引き戻しの compact comma の filtered 性。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：compact 成分を持つ小さい slice 図式は同じ性質の先端を持つ全余錐へ延長できる。
方針：元の底で全入力付き compact 成分を交互構成し、第一脚で比較同型を持ち上げる。
規約：元の全図式を保持し、二成分と底には filtered 余極限だけを要求する。
使われ方：compact comma の μ-filtered 性の全小試験。 -/
lemma exists_componentCompactSliceCocone_of_accessible_components
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {K : SSet.{u}} [Quasicategory K] (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ E) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ D)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ B)
    (hEκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ E)
    (hDκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ D)
    (hBκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ B)
    (hpμ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ p) (hqμ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ q)
    (hpκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ p) (hqκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ q)
    (hpCompact : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ v →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app (Opposite.op ⦋0⦌) v))
    (hqCompact : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ v →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.app (Opposite.op ⦋0⦌) v))
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    (U : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (hU : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q
      ((U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) v)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone U, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) c.vertex) := by
  letI := hp.innerFibration
  let a := U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x
  let z := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone U
  let C : Fin 2 → SSet.{u + 1} := ![E, D]
  let pc : ∀ c, C c ⟶ B := by
    refine Fin.cases ?_ (Fin.cases ?_ (fun i ↦ Fin.elim0 i))
    · exact p
    · exact q
  let ac : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C c := by
    refine Fin.cases ?_ (Fin.cases ?_ (fun i ↦ Fin.elim0 i))
    · exact a ≫ pullback.fst p q
    · exact a ≫ pullback.snd p q
  let zc : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (ac c) := by
    refine Fin.cases ?_ (Fin.cases ?_ (fun i ↦ Fin.elim0 i))
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.fst p q) z
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.snd p q) z
  let r := (a ≫ pullback.fst p q) ≫ p
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.fst p q) z)
  have hi : ∀ c, Quasicategory (C c) := by
    refine Fin.cases ?_ (Fin.cases ?_ (fun i ↦ Fin.elim0 i))
    · change Quasicategory E; infer_instance
    · change Quasicategory D; infer_instance
  letI := hi
  have hC : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ (C c) := by intro c; fin_cases c; exact hE; exact hD
  have hCκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ (C c) := by
    intro c; fin_cases c; exact hEκ; exact hDκ
  have hpc : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (pc c) := by
    intro c; fin_cases c; exact hpμ; exact hqμ
  have hpcκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (pc c) := by
    intro c; fin_cases c; exact hpκ; exact hqκ
  have hcpc : ∀ c, ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ v →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((pc c).app (Opposite.op ⦋0⦌) v) := by
    intro c; fin_cases c; exact hpCompact; exact hqCompact
  have hca : ∀ c, ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((ac c).app (Opposite.op ⦋0⦌) v) := by
    intro c v
    fin_cases c
    · exact (hU v).1
    · exact (hU v).2
  have har : ∀ c, ac c ≫ pc c = r := by
    intro c
    fin_cases c
    · rfl
    · change (a ≫ pullback.snd p q) ≫ q = (a ≫ pullback.fst p q) ≫ p
      simp only [Category.assoc, pullback.condition]
  have hzt : ∀ c, (zc c).val ≫ pc c = t.val := by
    intro c
    fin_cases c
    · rfl
    · change (z.val ≫ pullback.snd p q) ≫ q = (z.val ≫ pullback.fst p q) ≫ p
      simp only [Category.assoc, pullback.condition]
  obtain ⟨v, hc, _, ⟨he⟩⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_compactInputColimitComparison_of_isKappaAccessible_base h hK hB
      C hC hCκ hBκ pc hpc hpcκ hcpc ac hca r har zc t hzt
  obtain ⟨w, hw⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_compactInputPullbackSliceVertex_of_compatible_components
    μ p q a z hp (har 1) (hzt 1) (v 0) (v 1) (hc 0) (hc 1) he
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_sliceCocone_of_inputVertex U w
  exact ⟨c, hc.symm ▸ hw⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
