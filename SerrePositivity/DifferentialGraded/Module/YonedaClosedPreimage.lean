module
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor
/-!
概要：代表加群間の実閉射の Yoneda 逆像を、元の全 Hom 同型で指定する。
方針：閉射を単位複体からの射として読み、Yoneda 評価と合成する。
規約：像は元の同じ加群閉射へ厳密に戻り、対象輸送を追加しない。
使われ方：c′ の行有限行列の元の dg 圏における係数を固定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

def dgYonedaClosedPreimage {x y : D}
    (f : ForgetEnrichment.of (Complex R) (representable R x) ⟶
      ForgetEnrichment.of (Complex R) (representable R y)) :
    ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y :=
  ForgetEnrichment.homOf (Complex R)
    (ForgetEnrichment.homTo (Complex R) f ≫ (dgYonedaIso R x (representable R y)).hom)

lemma dgYonedaClosedPreimage_map {x y : D}
    (f : ForgetEnrichment.of (Complex R) (representable R x) ⟶
      ForgetEnrichment.of (Complex R) (representable R y)) :
    (dgYoneda R D).onClosed.map (dgYonedaClosedPreimage R D f) = f := by
  change (ForgetEnrichment.homTo (Complex R) f ≫ (dgYonedaIso R x (representable R y)).hom) ≫
    (dgYonedaIso R x (representable R y)).inv = ForgetEnrichment.homTo (Complex R) f
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.DifferentialGraded
