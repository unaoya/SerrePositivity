module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridLowerSeedCorner

/-!
概要：同じ格子長方形の余錐と native 下方余錐を厳密に比較する。
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
variable {P : Type u} [PartialOrder P]

def excisionGridLowerRectangleCocone :
    JoinCocone (nerveMap
      (posetSubtypeLowerProjection IsExcisionGridSeed (excisionGridCorePoint.{u} 2 1)) ≫
        nerveMap excisionGridSeedInclusion) := by
  let d := (pastingCocone excisionGridLowerRectangle).restrict
    excisionGridLowerSeedCornerIso.hom
  refine ⟨d.val, d.property.trans ?_⟩
  exact excisionGridLowerSeedCornerIso_projection

lemma excisionGridLowerRectangleCocone_vertex :
    excisionGridLowerRectangleCocone.{u}.vertex =
      nerveVertex (excisionGridCorePoint 2 1) := by
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridLowerRectangleCocone_val :
    excisionGridLowerRectangleCocone.{u}.val =
      (posetSubtypeLowerCocone IsExcisionGridSeed (excisionGridCorePoint 2 1)).val := by
  apply thinNerveCocone_val_eq_of_vertex
  rw [excisionGridLowerRectangleCocone_vertex, posetSubtypeLowerCocone_vertex]

end SerrePositivity.InfinityCategories
