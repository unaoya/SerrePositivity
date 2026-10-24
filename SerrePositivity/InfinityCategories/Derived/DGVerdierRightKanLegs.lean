module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRightKanCanonical
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverLimitLegs
public import SerrePositivity.InfinityCategories.Derived.ConeLegRestriction
public import SerrePositivity.InfinityCategories.F1B.KanRightConstantFamily
/-!
概要：任意反転関手の商の右 Kan 局所極限錐は、実逆分母の各指定値で同じ脚が可逆。
方針：cofinal な実分母制限を元の全図式へ厳密に戻し、実分母極限錐の脚を回収する。
規約：選ばれた実逆分母図式と全頂点を保持。使われ方：任意右 Kan 単位の同じ実成分の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 実右 Kan 極限錐の同じ実逆分母における脚は、元の同じ実辺として可逆。 -/
lemma dgVerdierRightKanLimitCone_leg_isInvertible (P : Set D)
    (hP : DGQuotient.localKFlat A D P) (x : D) {Y : SSet.{max u v}} [Quasicategory Y]
    (F : dgNerve A D ⟶ Y) (hF : InvertsEdges F (dgVerdierEdges A D P))
    (c : JoinCone (rightKanDiagram (dgQuotientNerveProjection A D P) F
      (Simplex.vertex ((DGQuotient.inclusion A D P).obj x)))) (hc : IsLimitCone c)
    (R : DGVerdierRightKanDiagram A D P hP x) (i : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    IsInvertibleEdge (F2.nativeConeLeg c
      ((dgVerdierRightKanMap A D P hP x R).app (Opposite.op ⦋0⦌) i)) := by
  let u := dgVerdierRightKanMap A D P hP x R
  have hu := dgVerdierRightKanMap_isLeftCofinal A D P hP x R
  have he : u ≫ rightKanDiagram (dgQuotientNerveProjection A D P) F
      (Simplex.vertex ((DGQuotient.inclusion A D P).obj x)) =
        dgVerdierOverSource A D P x ≫ F := by
    rw [rightKanDiagram, ← Category.assoc, dgVerdierRightKanMap_projection]
  let d : JoinCone (dgVerdierOverSource A D P x ≫ F) :=
    ⟨(restrictJoinCone c u).val, (restrictJoinCone c u).property.trans he⟩
  have hd : IsLimitCone d := (F1B.kanIsLimitCone_congr he (restrictJoinCone c u) d rfl).mp
    ((isLimitCone_iff_restrict_of_leftCofinal u hu _ c).mp hc)
  have h := dgVerdierOverLimitCone_leg_isInvertible A D P x F hF d hd i
  have he' : (F2.nativeConeLeg d i).edge =
      (F2.nativeConeLeg c (u.app (Opposite.op ⦋0⦌) i)).edge := nativeConeLeg_restrict_edge c u i
  exact (isInvertibleEdge_congr he').mp h
end SerrePositivity.InfinityCategories
