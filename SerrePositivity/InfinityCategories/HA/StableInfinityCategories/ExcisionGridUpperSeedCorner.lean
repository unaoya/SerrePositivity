module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreTranspose
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridLowerSeedCorner

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

abbrev ExcisionGridUpperSeed :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint.{u} 1 2)

def excisionGridUpperLowerSeedOrderIso :
    ExcisionGridUpperSeed.{u} ≃o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridLowerSeed.{u} where
  toFun p := ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreTranspose p.val, by
    constructor
    · have hp := p.property.1
      change _ + _ ≤ 2 at hp ⊢
      exact (Nat.add_comm _ _).trans_le hp
    · exact ⟨p.property.2.2, p.property.2.1⟩⟩
  invFun p := ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreTranspose p.val, by
    constructor
    · have hp := p.property.1
      change _ + _ ≤ 2 at hp ⊢
      exact (Nat.add_comm _ _).trans_le hp
    · exact ⟨p.property.2.2, p.property.2.1⟩⟩
  left_inv p := Subtype.ext (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreTranspose.left_inv p.val)
  right_inv p := Subtype.ext (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreTranspose.right_inv p.val)
  map_rel_iff' := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreTranspose.map_rel_iff'

def excisionGridUpperRectangle : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerRectangle ≫ nerveMap (⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreTranspose,
    fun _ _ h ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreTranspose.map_rel_iff'.mpr h⟩ :
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} →o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u}).toFunctor

def excisionGridUpperSeedCornerIso : nerve ExcisionGridUpperSeed.{u} ≅
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) :=
  PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of ExcisionGridUpperSeed.{u})
      (β := PartOrd.of _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridLowerSeed.{u}) excisionGridUpperLowerSeedOrderIso) ≪≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerSeedCornerIso

lemma excisionGridUpperSeedCornerIso_projection :
    excisionGridUpperSeedCornerIso.{u}.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ excisionGridUpperRectangle =
      nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerProjection _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 1 2)) ≫
        nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSeedInclusion := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  intro v
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
