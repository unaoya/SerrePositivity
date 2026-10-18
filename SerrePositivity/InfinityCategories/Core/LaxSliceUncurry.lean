module

public import SerrePositivity.InfinityCategories.Core.LaxSliceInputs

/-!
概要：太い slice への射を右図式を固定した太い join 上の関手へ戻す。
方針：普遍族を左因子と円柱上で評価して二つの pushout に貼る。
規約：右因子上では元の図式 p。
使われ方：Kerodon §4.6.6 の太い slice の普遍性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：太い slice の族は右因子上で固定図式に定値。
方針：fiber の包含の射影を uncurry する。
規約：パラメーターと標的の quasicategory 性は不要。
使われ方：Kerodon §4.6.6 の太い join の一端の貼り合わせ。 -/
lemma laxSliceFamily_fixed {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ laxSlice p) :
    (fatJoinInr (Δ[0] : SSet.{u}) K ▷ A) ≫
      uncurry (f ≫ vertexFiberι _ (functorVertex p)) = fst K A ≫ p := by
  rw [← uncurry_pre_app, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨k, a⟩
  dsimp [uncurry, functorVertex]
  rfl

/-- 概要：太い slice への射を右図式を固定する fat join 上の射へ uncurry する。
方針：左成分と円柱を普遍族で評価し、fat join の普遍性で貼る。
規約：右成分は p。
使われ方：Kerodon §4.6.6 の太い slice の普遍性。 -/
noncomputable def laxSliceUncurry {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ laxSlice p) : fatJoin A K ⟶ X :=
  fatJoinDesc
    (laxSliceLeftInput A K ≫ uncurry (f ≫ vertexFiberι _ (functorVertex p))) p
    (laxSliceCylinderInput A K ≫ uncurry (f ≫ vertexFiberι _ (functorVertex p)))
    (by rw [← Category.assoc, laxSliceCylinderInput_zero, Category.assoc])
    (by rw [← Category.assoc, laxSliceCylinderInput_one, Category.assoc, laxSliceFamily_fixed]; rfl)

/-- 概要：太い slice の uncurry は右図式を固定する。
方針：fat join の貼り合わせの右因子の計算。
規約：右図式は p。
使われ方：Kerodon §4.6.6 の固定図式の条件。 -/
lemma laxSliceUncurry_fixed {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ laxSlice p) :
    fatJoinInr A K ≫ laxSliceUncurry f = p := fatJoinInr_desc _ _ _ _ _

/-- 概要：太い slice の uncurry の左因子上の値は普遍族の左端の評価。
方針：fat join の貼り合わせの左因子の計算。
規約：パラメーターを保持する。
使われ方：Kerodon §4.6.6 の普遍性の計算。 -/
lemma laxSliceUncurry_inl {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ laxSlice p) :
    fatJoinInl A K ≫ laxSliceUncurry f =
      laxSliceLeftInput A K ≫ uncurry (f ≫ vertexFiberι _ (functorVertex p)) :=
  fatJoinInl_desc _ _ _ _ _

/-- 概要：太い slice の uncurry の円柱上の値は普遍族の円柱での評価。
方針：fat join の貼り合わせの円柱の計算。
規約：区間の座標を保つ。
使われ方：Kerodon §4.6.6 の普遍性の計算。 -/
lemma laxSliceUncurry_cylinder {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ laxSlice p) :
    fatJoinCylinder A K ≫ laxSliceUncurry f =
      laxSliceCylinderInput A K ≫ uncurry (f ≫ vertexFiberι _ (functorVertex p)) :=
  fatJoinCylinder_desc _ _ _ _ _

end SerrePositivity.InfinityCategories
