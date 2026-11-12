module
public import SerrePositivity.KST.Fibration.WeakStringFiniteComparison
public import SerrePositivity.KST.Fibration.WeakStringCofiberSource
public import SerrePositivity.KST.Fibration.WeakStringOneEquivalence
public import SerrePositivity.KST.Fibration.WeakArrowAdditivity

/-! # 有限列比較の一辺の場合の加法性同値

一因子の有限積を元の因子へ戻し、初期頂点・共通 cofiber の射対を既存の K-1 と照合する。
比較の元の二成分を固定して、正の全有限反復で局所化同型を証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 一辺の場合の有限積を元の因子へ戻すと、元の初期頂点と cofiber の射対を得る。 -/
lemma weakStringFiniteComparison_one_normalize {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    weakStringFiniteComparison q 1 r ≫ (𝟙 _ ⊗ₘ
      (productUniqueIso (fun _ : Fin 1 =>
        (multiRealizationFunctor r).obj (closedStableModel (kernelClosedPredicate q)))).hom) =
      lift ((multiRealizationFunctor r).map (weakStringVertexTopExact q ⦋1⦌ 0))
        (weakStringCofiberMultiMap q (𝟙 ⦋1⦌) r) := by
  unfold weakStringFiniteComparison
  rw [lift_map, Category.comp_id, productUniqueIso_hom,
    weakStringConsecutiveCofibers_projection, consecutiveWeakStringEdge_one]

/-- 元の一辺の二評価の射対は、既存の W 辺の加法性写像そのものである。 -/
lemma weakStringOnePair_eq_additivity {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    lift ((multiRealizationFunctor (r + 1)).map (weakStringVertexTopExact q ⦋1⦌ 0))
      (weakStringCofiberMultiMap q (𝟙 ⦋1⦌) (r + 1)) =
        (multiRealizationFunctor (r + 1)).map (weakStringEdgeExact q (𝟙 ⦋1⦌)) ≫
          weakArrowMultiAdditivityMap q r := by
  unfold weakArrowMultiAdditivityMap
  rw [← Category.assoc]
  change lift _ _ = (_ ≫ _) ≫ lift _ _
  rw [comp_lift]
  apply congrArg₂ lift
  · rw [← Functor.map_comp, ← Functor.map_comp]
    exact (congrArg (multiRealizationFunctor (r + 1)).map
      (weakStringCofiberSubobject_eq q (𝟙 ⦋1⦌))).symm
  · rw [← Functor.map_comp, ← Functor.map_comp]
    rfl

/-- 元の有限列比較の一辺の場合は、全正有限反復で局所化同型。 -/
theorem weakStringFiniteComparison_one_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (weakStringFiniteComparison q 1 (r + 1))) := by
  let Q := AnodyneHomotopy.anodyneQ
  let p := 𝟙 ((multiRealizationFunctor (r + 1)).obj
      (closedStableModel (ClosedStablePredicate.top (sInputModel B)))) ⊗ₘ
    (productUniqueIso (fun _ : Fin 1 => (multiRealizationFunctor (r + 1)).obj
      (closedStableModel (kernelClosedPredicate q)))).hom
  have : IsIso p := by
    change IsIso (𝟙 _ ⊗ₘ (productUniqueIso (fun _ : Fin 1 =>
      (multiRealizationFunctor (r + 1)).obj (closedStableModel (kernelClosedPredicate q)))).hom)
    infer_instance
  have : IsIso (Q.map p) := inferInstance
  have : IsIso (Q.map ((multiRealizationFunctor (r + 1)).map
      (weakStringEdgeExact q (𝟙 ⦋1⦌)))) :=
    multiRealization_map_localized_isIso_of_equivalence r (weakStringOneArrowEquivalence q)
  have : IsIso (Q.map (weakArrowMultiAdditivityMap q r)) :=
    weakArrowMultiAdditivityMap_localized_isIso q r
  have hn : IsIso (Q.map (weakStringFiniteComparison q 1 (r + 1) ≫ p)) := by
    change IsIso (Q.map (weakStringFiniteComparison q 1 (r + 1) ≫ (𝟙 _ ⊗ₘ _)))
    rw [weakStringFiniteComparison_one_normalize, weakStringOnePair_eq_additivity,
      Q.map_comp]
    infer_instance
  rw [Q.map_comp] at hn
  exact (isIso_comp_right_iff _ _).mp hn

end SerrePositivity.KST.Fibration
