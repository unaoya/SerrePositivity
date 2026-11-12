module
public import SerrePositivity.KST.SConstruction.SExactEnrichedFunctor
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramOrdinaryFunctor

/-! # 全高次比較を持つ元の豊穣 S• 図式
概要：元の各 S_n と面退化を、全高次 Hom に自然な比較の圏で単体的図式に束ねる。
方針：同じ完全関手族の内部 Hom 作用と元の添字制限の全パラメータ自然性を使う。
規約：元の安定値・完全射を変更しない。使われ方：厳密 dg 入力の豊穣 S• の包装。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 元の完全関手空間の作用を、同じ全関手空間で表示する実 S_n 豊穣関手。 -/
def sExactQuasicategoryEnrichedFunctor (n : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u} where
  obj C := ⟨sConstruction n C.obj, inferInstance⟩
  map C D := sExactFamilyMap n C D
  map_id C := sExactFamilyMap_unit n C
  map_comp C D E := (sExactFamilyMap_comp n C D E).symm

/-- 元の面退化は、同じ全高次完全関手族に関して自然な実比較である。 -/
def sExactQuasicategoryRestriction {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison (sExactQuasicategoryEnrichedFunctor.{u} n)
      (sExactQuasicategoryEnrichedFunctor m) := by
  refine ⟨fun C => sMap C.obj θ, ?_⟩
  intro C D
  change (sMap C.obj θ ▷ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u})) ≫
    uncurry (sExactFamilyMap m C D) = uncurry (sExactFamilyMap n C D) ≫ sMap D.obj θ
  simp only [sExactFamilyMap, uncurry_curry]
  exact (by simpa only [tensorHom_id] using (sExactFamilyAction_sMap C D θ).symm)

/-- 元の全高次比較を射として持つ圏における、同じ実 S• の単体的図式。 -/
def sExactSimplicialEnrichedFunctor :
    SimplicialObject (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) where
  obj n := sExactQuasicategoryEnrichedFunctor n.unop.len
  map f := sExactQuasicategoryRestriction f.unop.toOrderHom
  map_id n := by
    apply Subtype.ext
    funext C
    exact sMap_id n.unop.len C.obj
  map_comp f g := by
    apply Subtype.ext
    funext C
    exact sMap_comp C.obj g.unop.toOrderHom f.unop.toOrderHom

/-- 単体的図式の各段は、元の同じ全完全関手族を持つ S_n。 -/
lemma sExactSimplicialEnrichedFunctor_obj (n : SimplexCategoryᵒᵖ) :
    (sExactSimplicialEnrichedFunctor.{u}).obj n =
      sExactQuasicategoryEnrichedFunctor n.unop.len := rfl

/-- 全ての面退化の成分は、元の同じ実 S_n 添字制限。 -/
lemma sExactSimplicialEnrichedFunctor_map {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    ((sExactSimplicialEnrichedFunctor.{u}).map f).val C = sMap C.obj f.unop.toOrderHom := rfl

end SerrePositivity.KST.SConstruction
