module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridRightCocone

/-!
概要：native 局所余極限から full 比較格子の (3,2) 面の押し出し性を得る。
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

lemma ExcisionGridExtension.right_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    IsPushoutSquare (excisionGridRightSquare ≫ d.full) := by
  have he := (isColimitCone_iff_restrict_of_isIso _
    excisionGridRightSpanShapeIso.hom).mp d.right_span_colimit
  apply (isColimitCone_iff_of_val_eq _ _ ?_).mpr he
  change (spanCoconeSquareIso.hom ≫ excisionGridRightSquare) ≫ d.full =
    (((posetSubtypeLowerCocone IsExcisionGridMiddle excisionGridPoint32).restrict
      _).restrict excisionGridRightSpanShapeIso.hom).val ≫ d.full
  exact congrArg (fun f ↦ f ≫ d.full) excisionGridRightCocone_val.symm

end SerrePositivity.InfinityCategories
