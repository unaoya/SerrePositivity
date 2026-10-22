module
public import SerrePositivity.InfinityCategories.Stable.PosetOrderIsoCanonicalColimit
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridRightPushout

/-!
概要：座標交換と実局所余極限の移送で (2,3) 面の押し出し性を得る。
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

def excisionGridTranspose : ExcisionGridIndex.{u} ≃o ExcisionGridIndex.{u} where
  toFun p := ULift.up ⟨p.down.val.swap, p.down.property.2, p.down.property.1⟩
  invFun p := ULift.up ⟨p.down.val.swap, p.down.property.2, p.down.property.1⟩
  left_inv p := by apply ULift.ext; apply Subtype.ext; exact Prod.swap_swap _
  right_inv p := by apply ULift.ext; apply Subtype.ext; exact Prod.swap_swap _
  map_rel_iff' := by intro a b; exact and_comm

lemma excisionGridMiddle_transpose (p : ExcisionGridIndex.{u}) :
    IsExcisionGridMiddle (excisionGridTranspose p) ↔ IsExcisionGridMiddle p := by
  dsimp only [IsExcisionGridMiddle, IsExcisionGridCore, excisionGridTranspose,
    RelIso.coe_fn_mk, Equiv.coe_fn_mk, Prod.fst_swap, Prod.snd_swap]
  omega

lemma excisionGridRightSquare_pushout_of_canonical {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridIndex.{u} ⟶ X)
    (hF : ∀ p : (nerve ExcisionGridIndex.{u}) _⦋0⦌,
      IsColimitCone (leftKanCanonicalCocone (nerveMap excisionGridMiddleInclusion) F p)) :
    IsPushoutSquare (excisionGridRightSquare ≫ F) := by
  have hs := (isColimit_posetSubtypeLowerCocone_of_canonical IsExcisionGridMiddle
    excisionGridPoint32 F (hF (nerveVertex excisionGridPoint32))).restrict_of_rightAnodyne _
      excisionGridRightSpan_rightAnodyne
  have he := (isColimitCone_iff_restrict_of_isIso _ excisionGridRightSpanShapeIso.hom).mp hs
  apply (isColimitCone_iff_of_val_eq _ _ ?_).mpr he
  change (spanCoconeSquareIso.hom ≫ excisionGridRightSquare) ≫ F =
    (((posetSubtypeLowerCocone IsExcisionGridMiddle excisionGridPoint32).restrict
      _).restrict excisionGridRightSpanShapeIso.hom).val ≫ F
  exact congrArg (fun f ↦ f ≫ F) excisionGridRightCocone_val.symm

def excisionGridLeftSquare : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
    nerve ExcisionGridIndex.{u} :=
  excisionGridRightSquare ≫ nerveMap (posetOrderIsoFunctor excisionGridTranspose)

lemma ExcisionGridExtension.left_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    IsPushoutSquare (excisionGridLeftSquare ≫ d.full) := by
  have hT : (fun p ↦ IsExcisionGridMiddle (excisionGridTranspose.{u} p)) =
      IsExcisionGridMiddle := by
    funext p
    exact propext (excisionGridMiddle_transpose p)
  have hF : ∀ p : (nerve ExcisionGridIndex.{u}) _⦋0⦌,
      IsColimitCone (leftKanCanonicalCocone (nerveMap excisionGridMiddleInclusion)
        (nerveMap (posetOrderIsoFunctor excisionGridTranspose) ≫ d.full) p) := by
    intro p
    obtain ⟨p, rfl⟩ := nerveEquiv.symm.surjective p
    have h := posetSubtype_canonicalColimit_orderIso excisionGridTranspose
      IsExcisionGridMiddle p d.full (d.full_colimit (nerveVertex (excisionGridTranspose p)))
    rw [hT] at h
    exact h
  simpa only [excisionGridLeftSquare, Category.assoc] using
    excisionGridRightSquare_pushout_of_canonical
      (nerveMap (posetOrderIsoFunctor excisionGridTranspose) ≫ d.full) hF

end SerrePositivity.InfinityCategories
