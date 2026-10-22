module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridUpperSeedCorner

/-!
概要：上面の実余錐と native 下方余錐の厳密な比較。
方針：元の射影・実余錐・全単体の頂点式を保持して比較する。
規約：一般安定性の結論は先取りしない。使われ方：HA 1.4.2.15 の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

def excisionGridUpperRectangleCocone :
    JoinCocone (nerveMap
      (posetSubtypeLowerProjection IsExcisionGridSeed (excisionGridCorePoint.{u} 1 2)) ≫
        nerveMap excisionGridSeedInclusion) := by
  let d := (pastingCocone excisionGridUpperRectangle).restrict
    excisionGridUpperSeedCornerIso.hom
  refine ⟨d.val, d.property.trans ?_⟩
  exact excisionGridUpperSeedCornerIso_projection

lemma excisionGridUpperRectangleCocone_vertex :
    excisionGridUpperRectangleCocone.{u}.vertex =
      nerveVertex (excisionGridCorePoint 1 2) := by
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridUpperRectangleCocone_val :
    excisionGridUpperRectangleCocone.{u}.val =
      (posetSubtypeLowerCocone IsExcisionGridSeed (excisionGridCorePoint 1 2)).val := by
  apply thinNerveCocone_val_eq_of_vertex
  rw [excisionGridUpperRectangleCocone_vertex, posetSubtypeLowerCocone_vertex]

end SerrePositivity.InfinityCategories
