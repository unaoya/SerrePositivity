module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanHornIso
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LimitConeExtension
public import SerrePositivity.InfinityCategories.Core.SliceRestriction
public import SerrePositivity.InfinityCategories.Core.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCoreDiagram
public import SerrePositivity.InfinityCategories.Core.LeftPrism
public import SerrePositivity.InfinityCategories.Core.PrismFilling
public import SerrePositivity.InfinityCategories.Stable.PosetClosureRetraction

/-!
概要：比較格子の穿孔 core と元の cospan の実極限を比較する。
方針：固定した初期収縮と標準ホーンの全単体同型を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

def excisionCoreCospanBoundary : (horn 2 2 : SSet.{u}) ⟶
    nerve ExcisionCorePuncturedIndex.{u} :=
  excisionCoreCospanHornIso.hom ≫ nerveMap (posetSubtypeInclusion IsExcisionCoreCospan)

lemma excisionCoreCospanBoundary_leftAnodyne :
    leftAnodyneExtensions excisionCoreCospanBoundary.{u} := by
  have h : leftAnodyneExtensions
      (nerveMap (posetSubtypeInclusion IsExcisionCoreCospan.{u})) := by
    rw [← posetSubtypeNerveIso_hom_ι]
    exact leftAnodyneExtensions.comp_mem _ _
      (leftAnodyneExtensions.of_isIso _) excisionCoreCospan_leftAnodyne
  exact leftAnodyneExtensions.comp_mem _ _
    (leftAnodyneExtensions.of_isIso _) h

lemma excisionCoreCospanBoundary_mono : Mono excisionCoreCospanBoundary.{u} :=
  by
    unfold excisionCoreCospanBoundary
    infer_instance

lemma excisionCoreCospanBoundary_projection :
    excisionCoreCospanBoundary.{u} ≫
      nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) =
        cospanSquareBoundary ≫ grid22Face excisionGridCoreDiagram 2 2 := by
  apply horn₂₂.isPushout.hom_ext
  · simp only [excisionCoreCospanBoundary, excisionCoreCospanHornIso,
      ← Category.assoc, excisionCoreCospanFromHorn_first,
      cospanSquareBoundary_rightEdge]
    apply thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply Subtype.ext <;> apply Subtype.ext <;>
      apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide
  · simp only [excisionCoreCospanBoundary, excisionCoreCospanHornIso,
      ← Category.assoc, excisionCoreCospanFromHorn_second,
      cospanSquareBoundary_topEdge]
    apply thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply Subtype.ext <;> apply Subtype.ext <;>
      apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionCoreCospanBoundary_limit_iff {X : SSet.{u}} [Quasicategory X]
    {F : nerve ExcisionCorePuncturedIndex.{u} ⟶ X} (c : JoinCone F) :
    IsLimitCone c ↔ IsLimitCone (F2.restrictJoinCone c excisionCoreCospanBoundary) := by
  let := excisionCoreCospanBoundary_mono.{u}
  exact isLimitCone_iff_restrict_of_leftAnodyne c _
    excisionCoreCospanBoundary_leftAnodyne

end SerrePositivity.InfinityCategories
