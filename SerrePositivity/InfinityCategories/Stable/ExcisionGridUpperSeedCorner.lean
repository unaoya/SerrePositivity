module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCoreTranspose
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridLowerSeedCorner

/-!
概要：座標交換で上面の実下方添字を五頂点角と厳密に同定する。
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

abbrev ExcisionGridUpperSeed :=
  PosetSubtypeLowerIndex IsExcisionGridSeed (excisionGridCorePoint.{u} 1 2)

def excisionGridUpperLowerSeedOrderIso :
    ExcisionGridUpperSeed.{u} ≃o ExcisionGridLowerSeed.{u} where
  toFun p := ⟨excisionGridCoreTranspose p.val, by
    constructor
    · have hp := p.property.1
      change _ + _ ≤ 2 at hp ⊢
      exact (Nat.add_comm _ _).trans_le hp
    · exact ⟨p.property.2.2, p.property.2.1⟩⟩
  invFun p := ⟨excisionGridCoreTranspose p.val, by
    constructor
    · have hp := p.property.1
      change _ + _ ≤ 2 at hp ⊢
      exact (Nat.add_comm _ _).trans_le hp
    · exact ⟨p.property.2.2, p.property.2.1⟩⟩
  left_inv p := Subtype.ext (excisionGridCoreTranspose.left_inv p.val)
  right_inv p := Subtype.ext (excisionGridCoreTranspose.right_inv p.val)
  map_rel_iff' := excisionGridCoreTranspose.map_rel_iff'

def excisionGridUpperRectangle : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶
    nerve ExcisionGridCoreIndex.{u} :=
  excisionGridLowerRectangle ≫ nerveMap (⟨excisionGridCoreTranspose,
    fun _ _ h ↦ excisionGridCoreTranspose.map_rel_iff'.mpr h⟩ :
      ExcisionGridCoreIndex.{u} →o ExcisionGridCoreIndex.{u}).toFunctor

def excisionGridUpperSeedCornerIso : nerve ExcisionGridUpperSeed.{u} ≅
    (pastingCorner : SSet.{u}) :=
  PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of ExcisionGridUpperSeed.{u})
      (β := PartOrd.of ExcisionGridLowerSeed.{u}) excisionGridUpperLowerSeedOrderIso) ≪≫
        excisionGridLowerSeedCornerIso

lemma excisionGridUpperSeedCornerIso_projection :
    excisionGridUpperSeedCornerIso.{u}.hom ≫ pastingCorner.ι ≫ excisionGridUpperRectangle =
      nerveMap (posetSubtypeLowerProjection IsExcisionGridSeed (excisionGridCorePoint 1 2)) ≫
        nerveMap excisionGridSeedInclusion := by
  apply thinNerveHom_ext_of_vertices
  intro v
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

end SerrePositivity.InfinityCategories
