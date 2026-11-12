module
public import SerrePositivity.KST.SConstruction.DGGluingAxesArrows
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Size
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # 指定閉零二成分による実 gluing 零対象
概要：元の閉零二成分から作る同じ右軸対象は、実閉零圏でも零対象となる。
方針：加法的な元の右軸関手と Yoneda が閉零対象を保つことを使う。
規約：ホモトピー零だけでは代用しない。使われ方：二軸 cofiber の零角の代表加群化。
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

include hc hd

/-- 元の閉零二成分を持つ同じ実右軸対象は、閉零圏で零対象。 -/
lemma dgGluingClosedZero_isZero :
    IsZero (ForgetEnrichment.of (Complex R) (dgGluingRightAxisObject R C D M zc zd)) :=
  (dgGluingRightAxis R C D M zc hc).onClosed.map_isZero hd

/-- 同じ実 gluing 零対象の代表加群は、実閉零加群圏でも零対象。 -/
lemma dgGluingClosedZero_representable_isZero [Small.{u} D] :
    IsZero (ForgetEnrichment.of (Complex R)
      (representable R (dgGluingRightAxisObject R C D M zc zd))) :=
  (dgYoneda R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).onClosed.map_isZero
    (dgGluingClosedZero_isZero R C D M zc hc zd hd)

end SerrePositivity.KST.SConstruction
