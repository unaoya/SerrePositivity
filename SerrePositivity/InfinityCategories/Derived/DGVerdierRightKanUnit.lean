module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRightKanLegs
public import SerrePositivity.InfinityCategories.Derived.RightKanTransportComponents
/-!
概要：任意の実分母反転関手の実右 Kan 単位は、元の同じ全実成分が可逆。
方針：実恒等分母の値で標準錐と輸送錐の同じ二脚の可逆性を回収し、全錐の自然性を使う。
規約：独立な点ごとの同型や別の単位を選ばない。使われ方：全反転関手への本質的全射性。
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
/-- 元の恒等実分母は、右 Kan 形状の射影後にも元の同じ対象そのもの。 -/
lemma dgVerdierRightKanMap_identity_projection (P : Set D)
    (hP : DGQuotient.localKFlat A D P) (x : D) (R : DGVerdierRightKanDiagram A D P hP x) :
    (rightKanProjection (dgQuotientNerveProjection A D P)
      (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))).app (Opposite.op ⦋0⦌)
      ((dgVerdierRightKanMap A D P hP x R).app (Opposite.op ⦋0⦌)
        (dgVerdierOverIdentityVertex A D P x)) = Simplex.vertex x := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (dgVerdierRightKanMap_projection A D P hP x R) (Opposite.op ⦋0⦌))
      (dgVerdierOverIdentityVertex A D P x)
  exact h.trans (sliceIdentityCone_projection (X := dgNerve A D) (Simplex.vertex x))
/-- 任意の実右 Kan 単位の元の対象 x での同じ実成分は可逆。 -/
lemma dgVerdierRightKanUnit_vertex_isInvertible (P : Set D)
    (hP : DGQuotient.localKFlat A D P) {Y : SSet.{max u v}} [Quasicategory Y]
    (F : dgNerve A D ⟶ Y) (hF : InvertsEdges F (dgVerdierEdges A D P))
    (G : dgQuotientNerve A D P ⟶ Y)
    (α : SSet.Homotopy (dgQuotientNerveProjection A D P ≫ G) F)
    (hα : IsRightKanExtension (dgQuotientNerveProjection A D P) F G α) (x : D) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge α (Simplex.vertex x)).toTruncated := by
  obtain ⟨R⟩ := dgVerdierRightKanDiagram_nonempty A D P hP x
  obtain ⟨t, ht⟩ := hα (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))
  let i := dgVerdierOverIdentityVertex A D P x
  let v := (dgVerdierRightKanMap A D P hP x R).app (Opposite.op ⦋0⦌) i
  have hqG : InvertsEdges (dgQuotientNerveProjection A D P ≫ G) (dgVerdierEdges A D P) :=
    (dgQuotientNerveProjection_invertsVerdierEdges A D P hP).comp G
  have h₀ := dgVerdierRightKanLimitCone_leg_isInvertible A D P hP x _ hqG
    (rightKanCanonicalCone (dgQuotientNerveProjection A D P) G
      (Simplex.vertex ((DGQuotient.inclusion A D P).obj x)))
    (dgVerdierRightKanCanonicalCone_isLimit A D P hP x G) R i
  have h₁ := dgVerdierRightKanLimitCone_leg_isInvertible A D P hP x F hF t.cone ht R i
  have hi := t.component_isInvertible_of_legs v h₀ h₁
  have hp := dgVerdierRightKanMap_identity_projection A D P hP x R
  exact (congrArg (fun z => IsInvertibleEdge
    (simplicialHomotopyVertexEdge α z).toTruncated) hp).mp hi
/-- 任意反転関手の実右 Kan 単位の全実成分は、任意の元の頂点で可逆。 -/
lemma dgVerdierRightKanUnit_isInvertible (P : Set D)
    (hP : DGQuotient.localKFlat A D P) {Y : SSet.{max u v}} [Quasicategory Y]
    (F : dgNerve A D ⟶ Y) (hF : InvertsEdges F (dgVerdierEdges A D P))
    (G : dgQuotientNerve A D P ⟶ Y)
    (α : SSet.Homotopy (dgQuotientNerveProjection A D P ≫ G) F)
    (hα : IsRightKanExtension (dgQuotientNerveProjection A D P) F G α)
    (z : (dgNerve A D) _⦋0⦌) : IsInvertibleEdge (simplicialHomotopyVertexEdge α z).toTruncated := by
  let x := (dgNerve.vertexEquiv A D) z
  have hz : Simplex.vertex x = z := (dgNerve.vertexEquiv A D).symm_apply_apply z
  exact (congrArg (fun t => IsInvertibleEdge (simplicialHomotopyVertexEdge α t).toTruncated)
    hz).mp (dgVerdierRightKanUnit_vertex_isInvertible A D P hP F hF G α hα x)
end SerrePositivity.InfinityCategories
