module
public import SerrePositivity.KST.SConstruction.MultiSExactRestriction
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedDiagramPrecomposition

/-! # 元の有限反復 S の実 Quasi 値豊穣関手
概要：元の反復 S の全完全関手族を、同じ全内部 Hom で表示する。
方針：完全関手空間の実包含を使い、元の反復作用を通常射で回収する。
規約：全高次入力を保持する。使われ方：全多単体図式と実 core への持ち上げ。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 安定値を同じ実 Quasi 対象として含め、全完全関手族の包含を保持する。 -/
def stableQuasicategoryEnrichedInclusion :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u} where
  obj C := ⟨C.obj, inferInstance⟩
  map C D := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D).ι
  map_id C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity_ι C
  map_comp C D E := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition_ι C D E

/-- 元の有限反復 S の全完全関手族を、同じ全内部 Hom で保持する。 -/
def multiSQuasicategoryEnrichedFunctor (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u} :=
  (multiSExactEnrichedEndofunctor r d).comp SSet stableQuasicategoryEnrichedInclusion

/-- 全方向の元の反復値をそのまま回収する。 -/
lemma multiSQuasicategoryEnrichedFunctor_obj (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    ((multiSQuasicategoryEnrichedFunctor r d).obj C).obj =
      (multiSConstruction r (stableCategoryModel C)).obj d := rfl

/-- 通常の完全射では、同じ元の反復 S 射の curry を回収する。 -/
lemma multiSQuasicategoryEnrichedFunctor_hom (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F ≫ (multiSQuasicategoryEnrichedFunctor r d).map C D =
      curry' (C := SSet.{u}) (multiSExactMap r d F).hom := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F ≫ ((multiSExactEnrichedEndofunctor r d).map C D ≫ _) = _
  erw [← Category.assoc, multiSExactEnrichedEndofunctor_hom, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv_ι]

/-- 先頭方向の全族は、残りの反復全族と同じ元の S_n 全作用の合成。 -/
lemma multiSQuasicategoryEnrichedFunctor_map_succ (r : ℕ)
    (d : Fin (r + 1) → SimplexCategoryᵒᵖ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    (multiSQuasicategoryEnrichedFunctor (r + 1) d).map C D =
      multiSExactEnrichedMap r (fun i => d i.succ) C D ≫
        sExactFamilyMap (d 0).unop.len
          (multiSExactCategory r (fun i => d i.succ) C)
          (multiSExactCategory r (fun i => d i.succ) D) := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => multiSExactEnrichedMap r (fun i => d i.succ) C D ≫ f)
      (sExactEnrichedMap_inclusion (d 0).unop.len
        (multiSExactCategory r (fun i => d i.succ) C)
        (multiSExactCategory r (fun i => d i.succ) D)))

end SerrePositivity.KST.SConstruction
