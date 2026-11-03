module
public import SerrePositivity.InfinityCategories.Stable.InitialDiagramRestriction
public import SerrePositivity.InfinityCategories.F1.PastingRightCocone

/-! # 始点が始対象となる左 cone の余錐の制限

概要：一点と図式の join 上の図式で最初の頂点が始対象なら、右の図式への制限は余極限性を保ち反映する。
方針：coslice の curry に直して始対象を忘れる比較を使い、実際の余錐の射の等号で戻す。
規約：余錐の制限は既存の JoinCocone.restrict。使われ方：標準 span の零始点を除く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：始対象を先頭に持つ左 cone の余錐は、先頭を除いた余錐と余極限性が同値。
方針：始点の射を Yoneda 表示に直し、二重 coslice の射影と実際の制限を照合する。
規約：値域は quasicategory、図式の形状は任意。使われ方：零始点の span と二点図式の比較。 -/
lemma isColimitCone_iff_restrict_joinInr_of_initial {L X : SSet.{u}} [Quasicategory X]
    (F : join (Δ[0] : SSet.{u}) L ⟶ X)
    (hx : IsInitialVertex (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) L ≫ F)))
    (d : JoinCocone F) :
    IsColimitCone d ↔ IsColimitCone (d.restrict (joinInr (Δ[0] : SSet.{u}) L)) := by
  let x := SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) L ≫ F)
  have hf : joinInl (Δ[0] : SSet.{u}) L ≫ F = SSet.yonedaEquiv.symm x :=
    (SSet.yonedaEquiv.symm_apply_apply _).symm
  let c := sliceUnderCurry F hf
  have hc : sliceUnderUncurry c = F := sliceUnderUncurry_curry F hf
  let d' : JoinCocone (sliceUnderUncurry c) := ⟨d.val, by rw [hc]; exact d.property⟩
  let e : JoinCocone (c ≫ sliceUnderProjection (SSet.yonedaEquiv.symm x)) :=
    (diagramNestedCosliceProjection c).app (Opposite.op ⦋0⦌) d'
  have he : e.val = (d.restrict (joinInr (Δ[0] : SSet.{u}) L)).val :=
    diagramNestedCosliceProjection_val c d'
  exact (isColimitCone_iff_of_val_eq d d' rfl).trans
    ((isColimitCone_iff_forget_initial hx c d').trans
      (isColimitCone_iff_of_val_eq e (d.restrict (joinInr (Δ[0] : SSet.{u}) L)) he))

end SerrePositivity.InfinityCategories
