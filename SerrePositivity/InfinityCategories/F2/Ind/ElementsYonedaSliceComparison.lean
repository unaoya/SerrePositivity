module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityCocone
public import SerrePositivity.InfinityCategories.F2.Ind.ElementsCoconeComparison

/-!
概要：元の小さい元の圏から、同じ前層への Yoneda slice への一つの大域比較を構成する。
方針：構成した同じ native 密度余錐を slice へ curry し、元の射影と引き戻しに束ねる。
規約：全単体で底を厳密に保つ。比較の同値性と余極限性は別工程。
使われ方：密度余錐の各 fiber の検査と、κ-filtered 生成表示への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 同じ native 余錐の右端は、元の F を表す指定点そのもの。 -/
lemma presheafDensityCocone_fixed :
    joinInr ((SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening F))
      (Δ[0] : SSet.{u + 1}) ≫ (presheafDensityCocone F).val =
        SSet.yonedaEquiv.symm (functorVertex F) := by
  apply SSet.yonedaEquiv.injective
  exact ((presheafDensityCocone F).vertex_eq.symm.trans (presheafDensityCocone_vertex F)).trans
    (SSet.yonedaEquiv.apply_symm_apply (functorVertex F)).symm

/-- 同じ密度余錐を、元の F への slice 内の全族として読む。 -/
def presheafDensitySliceMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening F) ⟶
      sliceOver (SSet.yonedaEquiv.symm (functorVertex F)) :=
  sliceOverCurry (presheafDensityCocone F).val (presheafDensityCocone_fixed F)

/-- 同じ slice の全族の射影は、元の Yoneda 図式そのもの。 -/
lemma presheafDensitySliceMap_projection :
    presheafDensitySliceMap F ≫ sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F)) =
      presheafElementsYonedaDiagram F := by
  have h := sliceOverUncurry_projection (presheafDensitySliceMap F)
  rw [presheafDensitySliceMap, sliceOverUncurry_curry] at h
  exact h.symm.trans (presheafDensityCocone F).property

/-- 元の小さい元の圏から、同じ Yoneda slice への全高次の比較。 -/
def presheafElementsYonedaSliceComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening F) ⟶ presheafYonedaSlice F :=
  pullback.lift (presheafDensitySliceMap F)
    ((SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningProjection F))
    (presheafDensitySliceMap_projection F)

/-- 構成した同じ大域比較は、元の底を厳密に保つ。 -/
lemma presheafElementsYonedaSliceComparison_projection :
    presheafElementsYonedaSliceComparison F ≫ presheafYonedaSliceProjection F =
      (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningProjection F) :=
  pullback.lift_snd _ _ _

/-- 同じ比較から余錐を戻すと、構成済みの同じ小さい密度余錐そのもの。 -/
lemma presheafElementsYonedaSliceComparison_cocone :
    presheafElementsCoconeOfComparison F (presheafElementsYonedaSliceComparison F)
      (presheafElementsYonedaSliceComparison_projection F) = presheafDensityCocone F := by
  apply Subtype.ext
  simp only [presheafElementsCoconeOfComparison, presheafElementsYonedaSliceComparison,
    pullback.lift_fst, presheafDensitySliceMap, sliceOverUncurry_curry]

end SerrePositivity.InfinityCategories.F2.Ind
