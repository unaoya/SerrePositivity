module
public import SerrePositivity.KST.SConstruction.DGGluingLeftAxisHom
public import SerrePositivity.KST.SConstruction.DGGluingRightAxisHom

/-! # 元の対象と指定二軸の間の全 Hom 比較
概要：右軸から元の対象への Hom と、元の対象から左軸への Hom を元の二圏へ戻す。
方針：同じ代表加群 comma 表示の実零成分を消し、元の射影を順射として保持する。
規約：全整数次数の実鎖同型。使われ方：二軸への射の自然性と随伴比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
private lemma postIsoInverseCancel {V : Type*} [Category V] {A B K : V}
    (f : K ⟶ B) (e : A ≅ B) : (f ≫ e.inv) ≫ e.hom = f := by
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

/-- 元の右軸から任意の元の対象への全 Hom は、同じ右 Hom と実同型。 -/
def dgGluingFromRightAxisHomIso (z : C)
    (hz : IsZero (ForgetEnrichment.of (Complex R) z)) (d : D) (Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (dgGluingRightAxisObject R C D M z d) Y ≅
      homObject R D d Y.right :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M (dgGluingRightAxisObject R C D M z d) Y) ≪≫
  (dgCommaZeroSourceIso R D (RightModule R C) M.toFunctor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M (dgGluingRightAxisObject R C D M z d))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y)
    (dgRepresentableClosedZeroHom R z hz (representable R Y.left))
    (dgRepresentableClosedZeroHom R z hz (M.rightAt Y.right)))

/-- 同じ右軸からの Hom 同型の順射は、元の実右 Hom 射影。 -/
lemma dgGluingFromRightAxisHomIso_hom (z : C)
    (hz : IsZero (ForgetEnrichment.of (Complex R) z)) (d : D) (Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (dgGluingFromRightAxisHomIso R C D M z hz d Y).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M (dgGluingRightAxisObject R C D M z d) Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_right R C D M _ _

/-- 任意の元の対象から実左軸への全 Hom は、同じ左 Hom と実同型。 -/
def dgGluingToLeftAxisHomIso (z : D)
    (hz : IsZero (ForgetEnrichment.of (Complex R) z)) (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (c : C) :
    homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X (dgGluingLeftAxisObject R C D M z c) ≅
      homObject R C X.left c :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X (dgGluingLeftAxisObject R C D M z c)) ≪≫
    (dgCommaZeroReplacementIso R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M (dgGluingLeftAxisObject R C D M z c))
      (dgHom_isZero_of_closed_zero_target R z hz X.right)
      (dgBimoduleClosedZero_hom R C D M z hz (representable R X.left)))) ≪≫
    dgYonedaIso R X.left (representable R c)

/-- 同じ左軸への Hom 同型の順射は、元の実左 Hom 射影。 -/
lemma dgGluingToLeftAxisHomIso_hom (z : D)
    (hz : IsZero (ForgetEnrichment.of (Complex R) z)) (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (c : C) :
    (dgGluingToLeftAxisHomIso R C D M z hz X c).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X (dgGluingLeftAxisObject R C D M z c) := by
  have hh := congrArg (fun k => k ≫ (dgYonedaIso R X.left (representable R c)).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_left R C D M X (dgGluingLeftAxisObject R C D M z c))
  exact hh.trans (postIsoInverseCancel
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X (dgGluingLeftAxisObject R C D M z c))
    (dgYonedaIso R X.left (representable R c)))

end SerrePositivity.KST.SConstruction
