module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridFinalSpanProjection
public import SerrePositivity.InfinityCategories.F1.CoconeMappingPiZero

/-!
概要：同じ (3,3) を頂点とする実余錐と標準正方形の余錐の同定。
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
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def excisionGridFinalCocone : JoinCocone (pushoutSpan excisionGridFinalSquare.{u}) := by
  let d := (excisionGridFullPastCocone.restrict
    (fullSubcomplexOnVertices (nerve ExcisionGridFullPastIndex.{u})
      (fun v ↦ IsExcisionGridFinalSpan (nerveEquiv v))).ι).restrict
        excisionGridFinalSpanShapeIso.hom
  exact ⟨d.val, d.property.trans excisionGridFinalSpanShapeIso_projection⟩

lemma excisionGridFinalCocone_vertex : excisionGridFinalCocone.{u}.vertex =
    nerveVertex excisionGridPoint33 := by
  change ((excisionGridFullPastCocone.restrict
    _).restrict _).vertex = _
  rw [JoinCocone.vertex_restrict, JoinCocone.vertex_restrict, excisionGridFullPastCocone_vertex]

lemma excisionGridFinalCocone_val : excisionGridFinalCocone.{u}.val =
    (pushoutCocone excisionGridFinalSquare).val := by
  apply thinNerveCocone_val_eq_of_vertex
  rw [excisionGridFinalCocone_vertex, pushoutCocone_vertex]
  symm
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories
