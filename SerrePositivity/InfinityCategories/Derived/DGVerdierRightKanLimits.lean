module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRightKanCofinality
public import SerrePositivity.InfinityCategories.Derived.CofinalLimitTransfer
public import SerrePositivity.InfinityCategories.F1B.KanRightExistence
/-!
概要：任意の実分母反転関手について、商の全頂点で実右 Kan 局所極限を構成する。
方針：実逆分母の left cofinal 比較に沿って、実分母図式の既存極限を移送する。
規約：標的は任意 quasicategory。使われ方：全関手の右 Kan 拡張による組み立て。
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
/-- 元の対象の商像で、任意反転関手の実右 Kan 局所図式は極限を持つ。 -/
lemma dgVerdierRightKanDiagram_hasLimit (P : Set D) (hP : DGQuotient.localKFlat A D P)
    (x : D) {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) :
    HasLimit (rightKanDiagram (dgQuotientNerveProjection A D P) F
      (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))) := by
  obtain ⟨R⟩ := dgVerdierRightKanDiagram_nonempty A D P hP x
  apply hasLimit_of_leftCofinal (dgVerdierRightKanMap A D P hP x R)
    (dgVerdierRightKanMap_isLeftCofinal A D P hP x R)
  have he : dgVerdierRightKanMap A D P hP x R ≫
      rightKanDiagram (dgQuotientNerveProjection A D P) F
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj x)) =
          dgVerdierOverSource A D P x ≫ F := by
    rw [rightKanDiagram, ← Category.assoc, dgVerdierRightKanMap_projection]
  exact (congrArg HasLimit he).mpr (dgVerdierOver_hasLimit A D P x F hF)
/-- 任意反転関手の商の全頂点で、実右 Kan 局所極限が存在する。 -/
lemma dgVerdierRightKanDiagram_hasLimit_all (P : Set D) (hP : DGQuotient.localKFlat A D P)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) (z : (dgQuotientNerve A D P) _⦋0⦌) :
    HasLimit (rightKanDiagram (dgQuotientNerveProjection A D P) F z) := by
  let x := (dgNerve.vertexEquiv A (DGQuotient.QuotientObject D P)) z
  have hz : Simplex.vertex x = z := (dgNerve.vertexEquiv A _).symm_apply_apply z
  have h := dgVerdierRightKanDiagram_hasLimit A D P hP x.val F hF
  exact (congrArg (fun t => HasLimit
    (rightKanDiagram (dgQuotientNerveProjection A D P) F t)) hz).mp h
/-- 任意反転関手は、全商図式と実単位ホモトピーを持つ実右 Kan 拡張へ組み立つ。 -/
lemma dgVerdierInvertingFunctor_rightKanExtension_exists (P : Set D)
    (hP : DGQuotient.localKFlat A D P) {Y : SSet.{max u v}} [Quasicategory Y]
    (F : dgNerve A D ⟶ Y) (hF : InvertsEdges F (dgVerdierEdges A D P)) :
    ∃ (G : dgQuotientNerve A D P ⟶ Y) (α : SSet.Homotopy
      (dgQuotientNerveProjection A D P ≫ G) F),
        IsRightKanExtension (dgQuotientNerveProjection A D P) F G α :=
  F1B.exists_kanRightExtension_of_local_limits (dgQuotientNerveProjection A D P) F
    (dgVerdierRightKanDiagram_hasLimit_all A D P hP F hF)
end SerrePositivity.InfinityCategories
