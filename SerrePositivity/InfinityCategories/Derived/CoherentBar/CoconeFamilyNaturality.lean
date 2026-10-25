module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyCoordinates
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinNaturality
/-!
概要：混合 HA 単体の座標は、元の図式と余錐パラメーターの双方に自然である。
方針：join の二変数の自然性と、既存の coslice fiber の単体作用を使う。
規約：全単調写像を扱い、単射性や余錐の普遍性を仮定しない。
使われ方：高次 Hom 逆構成の面・退化との整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeFamilySimplex_map {a b n m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌)
    (α : ⦋a⦌ ⟶ ⦋n⦌) (β : ⦋b⦌ ⟶ ⦋m⦌) :
    dgCoherentBarCoconeFamilySimplex R D F y ((coconeMappingSpace F y).map β.op c)
      (I.map α.op s) =
    (dgCoherentBarCoconeFamilySimplex R D F y c s).pullback
      (dgCoherentBarJoinOrderMap α.toOrderHom β.toOrderHom) := by
  let A := (SSet.uliftFunctor.{max (u + 1) v, u}).obj I
  let f : (Δ[n] : SSet.{max (u + 1) v}) ⟶ A :=
    (SSet.yonedaEquiv (X := A)).symm (ULift.up s)
  have he : (SSet.yonedaEquiv (X := A)).symm (ULift.up (I.map α.op s)) =
      SSet.stdSimplex.map α ≫ f :=
    (SSet.yonedaEquiv_symm_naturality_left α (X := A) (ULift.up s)).symm
  have hi : SSet.stdSimplex.map
      (SimplexCategory.mkHom (dgCoherentBarJoinOrderMap α.toOrderHom β.toOrderHom)) ≫
      (joinStdSimplexIso.{max (u + 1) v} n m).inv =
      (joinStdSimplexIso a b).inv ≫
        joinMap (SSet.stdSimplex.map α) (SSet.stdSimplex.map β) := by
    apply (cancel_mono (joinStdSimplexIso.{max (u + 1) v} n m).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      dgCoherentBarJoinStdSimplex_naturality, Iso.inv_hom_id_assoc]
  change (SSet.yonedaEquiv (X := dgNerve R (RightModule R D)))
      ((joinStdSimplexIso.{max (u + 1) v} a b).inv ≫ joinMap
        ((SSet.yonedaEquiv (X := A)).symm (ULift.up (I.map α.op s))) (𝟙 Δ[b]) ≫
        (joinMap (𝟙 A) (SSet.stdSimplex.map β) ≫ c.val.val)) =
    (dgNerve R (RightModule R D)).map
      (SimplexCategory.mkHom (dgCoherentBarJoinOrderMap α.toOrderHom β.toOrderHom)).op
      ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D)))
        ((joinStdSimplexIso.{max (u + 1) v} n m).inv ≫ joinMap f (𝟙 Δ[m]) ≫ c.val.val))
  rw [he, SSet.yonedaEquiv_naturality]
  simp only [← Category.assoc]
  rw [hi]
  simp only [Category.assoc, ← joinMap_comp, Category.comp_id, Category.id_comp]

end SerrePositivity.InfinityCategories
