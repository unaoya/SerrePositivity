module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCenterSquare
public import SerrePositivity.InfinityCategories.Stable.CoconeMappingPiZero

/-!
概要：中央の実余錐と標準正方形の余錐を同じ頂点で同定する。
方針：同じ実図式の native 余錐と頂点を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の中央面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {P : Type u} [PartialOrder P]

def excisionGridCenterCocone : JoinCocone (pushoutSpan excisionGridCenterSquare.{u}) := by
  let d := (excisionGridPastCocone.restrict
    (fullSubcomplexOnVertices (nerve ExcisionGridPastIndex.{u})
      (fun v ↦ IsExcisionGridCenterSpan (nerveEquiv v))).ι).restrict
        excisionGridCenterSpanShapeIso.hom
  exact ⟨d.val, d.property.trans excisionGridCenterSpanShapeIso_projection⟩

lemma excisionGridCenterCocone_vertex : excisionGridCenterCocone.{u}.vertex =
    nerveVertex (excisionGridCorePoint 2 2) := by
  change ((excisionGridPastCocone.restrict _).restrict _).vertex = _
  rw [JoinCocone.vertex_restrict, JoinCocone.vertex_restrict, excisionGridPastCocone_vertex]

lemma excisionGridCenterCocone_val : excisionGridCenterCocone.{u}.val =
    (pushoutCocone excisionGridCenterSquare).val := by
  apply thinNerveCocone_val_eq_of_vertex
  rw [excisionGridCenterCocone_vertex, pushoutCocone_vertex]
  symm
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories
