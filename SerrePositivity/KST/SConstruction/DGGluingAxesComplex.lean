module
public import SerrePositivity.KST.SConstruction.DGGluingAxesArrows
public import Mathlib.Algebra.Homology.ShortComplex.Basic

/-! # 元の対象と指定二軸による実短複体
概要：元の右軸・対象・左軸と同じ二射を、合成零を持つ実短複体へ束ねる。
方針：元の右軸から左軸への全 Hom 零性で合成を消し、三対象と二射を保持する。
規約：cofiber 性・完全性は別工程。使われ方：二軸分解の元の短複体。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))

/-- 元の対象を通る右軸から左軸への二射の合成は、同じ閉零射そのもの。 -/
lemma dgGluingAxes_comp_zero (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingAxisRightInclusion R C D M zc hc X ≫
      dgGluingAxisLeftProjection R C D M zd hd X = 0 := by
  have hh : ForgetEnrichment.homTo (Complex R)
      (dgGluingAxisRightInclusion R C D M zc hc X ≫
        dgGluingAxisLeftProjection R C D M zd hd X) =
    ForgetEnrichment.homTo (Complex R) (0 :
      ForgetEnrichment.of (Complex R) (dgGluingRightAxisObject R C D M zc X.right) ⟶
      ForgetEnrichment.of (Complex R) (dgGluingLeftAxisObject R C D M zd X.left)) :=
    (dgGluingAxes_right_left_hom_isZero R C D M zc hc zd hd X.right X.left).eq_of_tgt _ _
  exact (ForgetEnrichment.homOf_homTo (Complex R) _).symm.trans
    ((congrArg (ForgetEnrichment.homOf (Complex R)) hh).trans
      (ForgetEnrichment.homOf_homTo (Complex R) _))

/-- 元の右軸・同じ対象・元の左軸と、同じ二射を保持する実短複体。 -/
def dgGluingAxesShortComplex (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    ShortComplex (ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)) :=
  ShortComplex.mk (dgGluingAxisRightInclusion R C D M zc hc X)
    (dgGluingAxisLeftProjection R C D M zd hd X)
    (dgGluingAxes_comp_zero R C D M zc hc zd hd X)

/-- 同じ実短複体の中央対象は、元の対象そのもの。 -/
lemma dgGluingAxesShortComplex_middle (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (dgGluingAxesShortComplex R C D M zc hc zd hd X).X₂ =
      ForgetEnrichment.of (Complex R) X := rfl

/-- 同じ実短複体の第一射は、元の実右軸からの同じ射。 -/
lemma dgGluingAxesShortComplex_f (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (dgGluingAxesShortComplex R C D M zc hc zd hd X).f =
      dgGluingAxisRightInclusion R C D M zc hc X := rfl

/-- 同じ実短複体の第二射は、元の実左軸への同じ射。 -/
lemma dgGluingAxesShortComplex_g (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (dgGluingAxesShortComplex R C D M zc hc zd hd X).g =
      dgGluingAxisLeftProjection R C D M zd hd X := rfl

end SerrePositivity.KST.SConstruction
