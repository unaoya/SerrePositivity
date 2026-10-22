module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCenterCocone

/-!
概要：native 左 Kan 局所余極限から比較格子の中央面の押し出し性を得る。
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

lemma ExcisionGridExtension.center_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    IsPushoutSquare (excisionGridCenterSquare ≫ d.core) := by
  have he := (isColimitCone_iff_restrict_of_isIso _
    excisionGridCenterSpanShapeIso.hom).mp d.center_span_colimit
  apply (isColimitCone_iff_of_val_eq _ _ ?_).mpr he
  change (spanCoconeSquareIso.hom ≫ excisionGridCenterSquare) ≫ d.core =
    ((excisionGridPastCocone.restrict _).restrict excisionGridCenterSpanShapeIso.hom).val ≫
      d.core
  exact congrArg (fun f ↦ f ≫ d.core) excisionGridCenterCocone_val.symm

end SerrePositivity.InfinityCategories
