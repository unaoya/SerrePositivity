module

public import SerrePositivity.InfinityCategories.Stable.SquareHomotopyCategory
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeNestedCosliceProjection
public import SerrePositivity.InfinityCategories.Stable.ReindexSliceUnder
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceTriangleFiber
public import SerrePositivity.InfinityCategories.F1.Simplicial.PrismEndpointRightAnodyne
public import SerrePositivity.InfinityCategories.Stable.CosliceRestriction

/-!
概要：元の pushout 四角形の全 coslice から入力 span への制限は自明 Kan fibration。
方針：標準四角形と span の右錐の同型を通して、余極限 coslice の制限に帰着する。
規約：指定四角形・指定 span・指定終点を保持する。
使われ方：HTT 5.5.5.13 の写像空間の fiber の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C)

/-- 元の四角形を展開した coslice の制限は、元の入力 span への通常の制限。 -/
lemma pushoutCosliceRestriction_eq :
    (sliceUnderReindexIso spanCoconeSquareIso R).hom ≫
        colimitCosliceRestriction (pushoutCocone R) =
      sliceUnderRestrict R spanSquareBoundary := by
  apply sliceUnderUncurry_injective
  rw [colimitCosliceRestriction_uncurry (p := pushoutSpan R) (pushoutCocone R)]
  have h : sliceUnderUncurry (sliceUnderReindexIso spanCoconeSquareIso R).hom =
      joinMap spanCoconeSquareIso.hom (𝟙 _) ≫ sliceUnderUncurry (𝟙 (sliceUnder R)) :=
    sliceUnderUncurry_restrict (𝟙 _) spanCoconeSquareIso.hom
  rw [h]
  change _ = sliceUnderUncurry ((𝟙 _) ≫ sliceUnderRestrict R spanSquareBoundary)
  rw [sliceUnderUncurry_restrict, ← Category.assoc, ← joinMap_comp, Category.id_comp]
  rfl

/-- pushout の元の四角形から入力 span への coslice 制限は全境界を持ち上げる。 -/
lemma pushoutCosliceRestriction_trivialKanFibration (hR : IsPushoutSquare R) :
    TrivialKanFibration (sliceUnderRestrict R spanSquareBoundary) := by
  rw [← pushoutCosliceRestriction_eq]
  have := colimitCosliceRestriction_trivialKanFibration (pushoutCocone R) hR
  exact ⟨trivialKanFibrations.comp_mem _ _ (MorphismProperty.rlp_of_isIso _ _)
    (TrivialKanFibration.mem (p := colimitCosliceRestriction (pushoutCocone R)))⟩

/-- 同じ pushout の制限は元の指定終点の余錐空間でも自明 Kan fibration。 -/
lemma pushoutCoconeMappingRestriction_trivialKanFibration
    (hR : IsPushoutSquare R) (y : C _⦋0⦌) :
    TrivialKanFibration (cosliceRestrictionFiberMap R spanSquareBoundary y) := by
  have := pushoutCosliceRestriction_trivialKanFibration R hR
  exact cosliceRestrictionFiberMap_trivialKanFibration R spanSquareBoundary y

/-- 四角形の上辺への包含は終点円柱の包含の反転であり、right anodyne である。 -/
lemma squareTopEdge_rightAnodyne : rightAnodyneExtensions (squareTopEdge :
    (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) := by
  have he : prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ (β_ Δ[1] Δ[1]).hom = squareTopEdge := rfl
  rw [← he]
  exact rightAnodyneExtensions.comp_mem _ _ (prismEndpoint_one_rightAnodyne Δ[1])
    (MorphismProperty.of_isIso _ _)

/-- 元の四角形の上辺への全 coslice 制限も自明 Kan fibration。 -/
lemma squareTopCosliceRestriction_trivialKanFibration [Quasicategory C] :
    TrivialKanFibration (sliceUnderRestrict R squareTopEdge) := by
  have : Mono (squareTopEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    intro a b h
    exact congrArg Prod.fst h
  exact sliceUnderRestrict_trivialKanFibration R squareTopEdge squareTopEdge_rightAnodyne

/-- 元の四角形の上辺への制限は、指定終点を固定しても自明 Kan fibration。 -/
lemma squareTopCoconeMappingRestriction_trivialKanFibration [Quasicategory C]
    (y : C _⦋0⦌) :
    TrivialKanFibration (cosliceRestrictionFiberMap R squareTopEdge y) := by
  have := squareTopCosliceRestriction_trivialKanFibration R
  exact cosliceRestrictionFiberMap_trivialKanFibration R squareTopEdge y

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
