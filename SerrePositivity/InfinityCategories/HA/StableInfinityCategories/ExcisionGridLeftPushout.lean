module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetOrderIsoCanonicalColimit
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRightPushout

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def excisionGridTranspose : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ≃o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} where
  toFun p := ULift.up ⟨p.down.val.swap, p.down.property.2, p.down.property.1⟩
  invFun p := ULift.up ⟨p.down.val.swap, p.down.property.2, p.down.property.1⟩
  left_inv p := by apply ULift.ext; apply Subtype.ext; exact Prod.swap_swap _
  right_inv p := by apply ULift.ext; apply Subtype.ext; exact Prod.swap_swap _
  map_rel_iff' := by intro a b; exact and_comm

lemma excisionGridMiddle_transpose (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle (excisionGridTranspose p) ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle p := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCore, excisionGridTranspose,
    RelIso.coe_fn_mk, Equiv.coe_fn_mk, Prod.fst_swap, Prod.snd_swap]
  omega

lemma excisionGridRightSquare_pushout_of_canonical {X : SSet.{u}} [Quasicategory X]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X)
    (hF : ∀ p : (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u}) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion) F p)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSquare ≫ F) := by
  have hs := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isColimit_posetSubtypeLowerCocone_of_canonical _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPoint32 F (hF (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPoint32))).restrict_of_rightAnodyne _
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSpan_rightAnodyne
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSpanShapeIso.hom).mp hs
  apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _ ?_).mpr he
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSquare) ≫ F =
    (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPoint32).restrict
      _).restrict _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSpanShapeIso.hom).val ≫ F
  exact congrArg (fun f ↦ f ≫ F) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightCocone_val.symm

def excisionGridLeftSquare : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSquare ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetOrderIsoFunctor excisionGridTranspose)

lemma ExcisionGridExtension.left_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension G z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (excisionGridLeftSquare ≫ d.full) := by
  have hT : (fun p ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle (excisionGridTranspose.{u} p)) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle := by
    funext p
    exact propext (excisionGridMiddle_transpose p)
  have hF : ∀ p : (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u}) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion)
        (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetOrderIsoFunctor excisionGridTranspose) ≫ d.full) p) := by
    intro p
    obtain ⟨p, rfl⟩ := nerveEquiv.symm.surjective p
    have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtype_canonicalColimit_orderIso excisionGridTranspose
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle p d.full (d.full_colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (excisionGridTranspose p)))
    rw [hT] at h
    exact h
  simpa only [excisionGridLeftSquare, Category.assoc] using
    excisionGridRightSquare_pushout_of_canonical
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetOrderIsoFunctor excisionGridTranspose) ≫ d.full) hF

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
