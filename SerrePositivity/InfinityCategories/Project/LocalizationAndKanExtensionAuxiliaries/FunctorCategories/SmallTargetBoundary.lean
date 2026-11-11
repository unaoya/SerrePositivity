module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SmallMarkedQuasicategoryHull
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacementNaturality
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SmallTargetDiagrams
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PositiveBoundaryFaithful
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseKan

/-!
概要：小さい標的での前合成の充満忠実性から、大きい標的での正次元境界を充填する。
方針：境界の二関手族・可逆 path 族・底単体を同じ marked 小模型へ厳密因子化する。
規約：小さい次数を持つ源・標的だけを仮定し、元の境界正方形を変更しない。
使われ方：Ind-S (4) の局所化普遍性の宇宙持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SmallSubcomplex

/-- 大きい標的の正次元境界資料を、同じ小模型内で充填して戻す。 -/
theorem precomposition_path_boundary_of_small_targets
    {A B : SSet.{max u v}} [∀ d, Small.{u} (A.obj d)] [∀ d, Small.{u} (B.obj d)]
    (F : A ⟶ B)
    (hF : ∀ (Q : SSet.{u}) [Quasicategory Q],
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre F).app ((SSet.uliftFunctor.{v, u}).obj Q)))
    (E : SSet.{max u v}) [Quasicategory E] (n : ℕ) :
    HasLiftingProperty (boundary (n + 1)).ι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap ((pre F).app E)) := by
  constructor
  intro a b sq
  let T : SSet.{max u v} := boundary (n + 1)
  let V : SSet.{max u v} := Δ[n + 1]
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (T.obj d) := by
    dsimp [T]
    infer_instance
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (V.obj d) := by
    dsimp [V]
    infer_instance
  have (d : SimplexCategoryᵒᵖ) : Small.{u} ((Δ[1] : SSet.{max u v}).obj d) := by
    infer_instance
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (((Δ[1] : SSet.{max u v}) ⊗ T).obj d) :=
    inferInstanceAs (Small.{u} (((Δ[1] : SSet.{max u v}).obj d) × T.obj d))
  have (d : SimplexCategoryᵒᵖ) : Small.{u} ((B ⊗ T).obj d) :=
    inferInstanceAs (Small.{u} (B.obj d × T.obj d))
  have (d : SimplexCategoryᵒᵖ) : Small.{u} ((A ⊗ V).obj d) :=
    inferInstanceAs (Small.{u} (A.obj d × V.obj d))
  have (d : SimplexCategoryᵒᵖ) : Small.{u}
      ((A ⊗ ((Δ[1] : SSet.{max u v}) ⊗ T)).obj d) :=
    inferInstanceAs (Small.{u} (A.obj d × (((Δ[1] : SSet.{max u v}) ⊗ T).obj d)))
  let p := (pre F).app E
  let a₀ : T ⟶ (ihom B).obj E := a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p
  let a₁ : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom A).obj E) :=
    a ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom A).obj E) 0) p
  let r := a₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((ihom A).obj E)
  let C := SSet.Subcomplex.range (uncurry a₀) ⊔
    SSet.Subcomplex.range (uncurry (uncurry r)) ⊔ SSet.Subcomplex.range (uncurry b)
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (C.obj d) := by
    have := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.small_range.{u} (uncurry a₀) d
    have := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.small_range.{u} (uncurry (uncurry r)) d
    have := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.small_range.{u} (uncurry b) d
    change Small.{u} ↥(((SSet.Subcomplex.range (uncurry a₀)).obj d ∪
      (SSet.Subcomplex.range (uncurry (uncurry r))).obj d) ∪
      (SSet.Subcomplex.range (uncurry b)).obj d)
    infer_instance
  let s : (T _⦋0⦌ × A _⦋0⦌) → E _⦋1⦌ := fun z => _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorPathPointEdge a₁ z.1 z.2
  have hs (z : T _⦋0⦌ × A _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (s z)) :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorPathPointEdge_invertible a₁ z.1 z.2
  let H := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.markedHull.{u, v} C s hs
  let Q := (SSet.uliftFunctor.{v, u}).obj H.obj
  let j : Q ⟶ E := H.inclusion
  letI := H.quasicategory
  have : Quasicategory Q := inferInstance
  have : Mono j := H.mono
  have : Mono ((ihom A).map j) := (ihom A).map_mono _
  have h₀ : SSet.Subcomplex.range (uncurry a₀) ≤ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.markedSeed C s hs :=
    le_trans (le_trans le_sup_left le_sup_left) le_sup_left
  have h₁ : SSet.Subcomplex.range (uncurry (uncurry r)) ≤ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.markedSeed C s hs :=
    le_trans (le_trans le_sup_right le_sup_left) le_sup_left
  have hb : SSet.Subcomplex.range (uncurry b) ≤ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.markedSeed C s hs :=
    le_trans le_sup_right le_sup_left
  obtain ⟨c₀, hc₀⟩ := H.factor_functor a₀ h₀
  obtain ⟨r', hr'⟩ := H.factor_functor (uncurry r) h₁
  have hr : curry r' ≫ (ihom (Δ[1] : SSet.{max u v})).map ((ihom A).map j) = r := by
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, hr']
  obtain ⟨c₁, hc₁⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.exists_functorPath_lift j a₁ (curry r') hr (by
    intro t k x y e he
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.markedHull_reflects_edge C s hs (t, k) e he)
  obtain ⟨d, hd⟩ := H.factor_functor b hb
  let q := (pre F).app Q
  have hn : q ≫ (ihom A).map j = (ihom B).map j ≫ p := ((pre F).naturality j).symm
  have hstart : c₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom A).obj Q) 0 = c₀ ≫ q := by
    apply (cancel_mono ((ihom A).map j)).1
    calc
      (c₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom A).obj Q) 0) ≫ (ihom A).map j =
          (c₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((ihom A).map j)) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom A).obj E) 0 := by
              simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint]
      _ = a₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom A).obj E) 0 := by rw [hc₁]
      _ = a₀ ≫ p := by
        dsimp [a₁, a₀, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection]
        rw [Category.assoc, pullback.condition, ← Category.assoc]
      _ = (c₀ ≫ (ihom B).map j) ≫ p :=
        (congrArg (fun z => z ≫ p) hc₀).symm
      _ = (c₀ ≫ q) ≫ (ihom A).map j := by
        simp only [Category.assoc, hn]
  let c : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement q := pullback.lift c₁ c₀ hstart
  have hcproj : c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection q = c₀ := pullback.lift_snd _ _ _
  have hend : c₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom A).obj Q) 1 = (boundary (n + 1)).ι ≫ d := by
    apply (cancel_mono ((ihom A).map j)).1
    calc
      (c₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom A).obj Q) 1) ≫ (ihom A).map j =
          (c₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((ihom A).map j)) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom A).obj E) 1 := by
              simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint]
      _ = a₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom A).obj E) 1 := by rw [hc₁]
      _ = (boundary (n + 1)).ι ≫ b := sq.w
      _ = ((boundary (n + 1)).ι ≫ d) ≫ (ihom A).map j := by
        rw [Category.assoc, hd]
  have sq' : CommSq c (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap q) d := by
    constructor
    change c ≫ (pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1) = _
    rw [← Category.assoc, pullback.lift_fst]
    exact hend
  have := (hF H.obj).equivalencePathReplacementMap.hasLiftingProperty_boundary_succ n
  let m := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementInduced q p ((ihom B).map j) ((ihom A).map j) hn
  have hm : c ≫ m = a := by
    apply pullback.hom_ext
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementInduced_path, ← Category.assoc,
        pullback.lift_fst, hc₁]
    · change (c ≫ m) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p = _
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementInduced_projection, ← Category.assoc,
        hcproj, hc₀]
      rfl
  refine CommSq.HasLift.mk' { l := sq'.lift ≫ m, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc, sq'.fac_left, hm]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementInduced_map, ← Category.assoc,
      sq'.fac_right, hd]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
