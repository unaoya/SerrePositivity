module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridRightSpanProjection

/-!
概要：同じ (3,2) を頂点とする実余錐と標準正方形の余錐を同定する。
方針：同じ実図式の native 余錐・頂点・二辺を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の外側の面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

def excisionGridRightCocone : JoinCocone (pushoutSpan excisionGridRightSquare.{u}) := by
  let d := ((posetSubtypeLowerCocone IsExcisionGridMiddle excisionGridPoint32).restrict
    (fullSubcomplexOnVertices (nerve ExcisionGridRightLowerIndex.{u})
      (fun v ↦ IsExcisionGridRightSpan (nerveEquiv v))).ι).restrict
        excisionGridRightSpanShapeIso.hom
  exact ⟨d.val, d.property.trans excisionGridRightSpanShapeIso_projection⟩

lemma excisionGridRightCocone_vertex : excisionGridRightCocone.{u}.vertex =
    nerveVertex excisionGridPoint32 := by
  change (((posetSubtypeLowerCocone IsExcisionGridMiddle excisionGridPoint32).restrict
    _).restrict _).vertex = _
  rw [JoinCocone.vertex_restrict, JoinCocone.vertex_restrict, posetSubtypeLowerCocone_vertex]

lemma excisionGridRightCocone_val : excisionGridRightCocone.{u}.val =
    (pushoutCocone excisionGridRightSquare).val := by
  apply thinNerveCocone_val_eq_of_vertex
  rw [excisionGridRightCocone_vertex, pushoutCocone_vertex]
  symm
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories
