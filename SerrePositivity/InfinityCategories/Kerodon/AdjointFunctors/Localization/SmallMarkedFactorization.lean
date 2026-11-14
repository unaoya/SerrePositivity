module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.SmallMarkedQuasicategoryHull
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseEdges

/-!
概要：大きい quasicategory への反転関手を、小さい反転関手へ厳密因子化する。
方針：元の図式の像と指定反転辺の逆三角形を同じ小模型に入れる。
規約：源の quasicategory 性は不要。底の図式と指定辺集合を変えない。
使われ方：Ind-S (4) の大きい標的への局所化延長。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization


/-- 指定辺の反転を保って、同じ実図式を小さい quasicategory へ厳密に因子化する。 -/
theorem exists_small_inverting_factorization {K : SSet.{u}} {E : SSet.{max u v}}
    [Quasicategory E] (f : (SSet.uliftFunctor.{v, u}).obj K ⟶ E)
    (W : Set (K _⦋1⦌)) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges f (ULift.up.{v, u} '' W)) :
    ∃ (Q : SSet.{u}) (_ : Quasicategory Q) (g : K ⟶ Q)
      (j : (SSet.uliftFunctor.{v, u}).obj Q ⟶ E),
      Mono j ∧ (SSet.uliftFunctor.{v, u}).map g ≫ j = f ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges g W := by
  let A := SSet.Subcomplex.range f
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (((SSet.uliftFunctor.{v, u}).obj K).obj d) :=
    small_of_injective (f := fun x => x.down) ULift.down_injective
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (A.obj d) := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.small_range.{u} f d
  let s : W → E _⦋1⦌ := fun w => f.app _ (ULift.up w.val)
  have hs (w : W) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (s w)) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ULift.up.{v, u} w.val)).map ((truncation 2).map f))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (s w)) rfl).mp
    exact hf (Set.mem_image_of_mem ULift.up w.property)
  let H := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.markedHull.{u, v} A s hs
  obtain ⟨g, hg⟩ := H.factor f (show A ≤ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.markedSeed A s hs from le_sup_left)
  refine ⟨H.obj, H.quasicategory, g, H.inclusion, H.mono, hg, ?_⟩
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertsEdges_ulift_iff g W).mp
  intro t ht
  obtain ⟨w, hw, rfl⟩ := ht
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.markedHull_reflects_edge A s hs (⟨w, hw⟩ : W)
  change H.inclusion.app _ (((SSet.uliftFunctor.{v, u}).map g).app _ (ULift.up w)) = s ⟨w, hw⟩
  have hh := congrArg (fun k : (SSet.uliftFunctor.{v, u}).obj K ⟶ E =>
    k.app (Opposite.op ⦋1⦌)) hg
  exact ConcreteCategory.congr_hom hh (ULift.up.{v, u} w)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.4.2" (partial := special) "仮定：単体集合と全辺、又は W を反転する与えられた関手（Lean が強い：任意の W で仮定なしの存在ではない）。結論：全辺の局所化、及び任意の W の小さい反転因数分解（Lean が弱い：後者は普遍性を要求しない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.exists_small_inverting_factorization
