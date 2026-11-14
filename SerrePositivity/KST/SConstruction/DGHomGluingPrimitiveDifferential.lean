module
public import SerrePositivity.KST.SConstruction.DGHomGluingActions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomComplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.ComplexHomotopies.ComplexMinusOneCochainBoundary

/-! # 元の gluing 第三成分の全次数微分
概要：mapping cocone の元の境界式を、同じ入力元の斉次等式に戻す。
方針：元の cochain 等式を評価し、左右の実射影と比較差を回収する。
規約：第三成分を零としない。使われ方：実 dg cone Hom 写像の鎖写像性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 元の第三成分は、入力の微分を左比較−右比較−自身の微分に送る。 -/
lemma dgGluingPrimitive_differential (n : ℤ)
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y).X n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y).v (n + 1) n (by omega)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y).d n (n + 1) a) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y).f n ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y).f n a) -
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y).f n ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y).f n a) -
        (M.value X.left Y.right).d (n - 1) n
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y).v n (n - 1) (by omega) a) := by
  have hb := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMinusOneCochain_boundary_apply
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y) _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive_boundary R C D M X Y) n a
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference, HomologicalComplex.comp_f, Preadditive.comp_sub,
    HomologicalComplex.sub_f_apply] at hb
  change _ + _ +
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y).f n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y).f n a) -
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y).f n
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y).f n a)) = 0 at hb
  apply sub_eq_zero.mp
  convert hb using 1
  abel

end SerrePositivity.KST.SConstruction
