module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridLowerRectangleCocone
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridExtension

/-!
概要：実左 Kan の局所余極限から格子の最初の右面の押し出し性を得る。
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

lemma excisionGridLowerRectangle_right_pushout {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (h : IsColimitCone (leftKanCanonicalCocone (nerveMap excisionGridSeedInclusion)
      F (nerveVertex (excisionGridCorePoint 2 1)))) :
    IsPushoutSquare (pastingSquare (excisionGridLowerRectangle ≫ F) 0) := by
  have hl := isColimit_posetSubtypeLowerCocone_of_canonical IsExcisionGridSeed
    (excisionGridCorePoint 2 1) F h
  have hc : IsColimitCone (mapJoinCocone F excisionGridLowerRectangleCocone) := by
    apply (isColimitCone_iff_of_val_eq _ _ ?_).mpr hl
    exact congrArg (fun f ↦ f ≫ F) excisionGridLowerRectangleCocone_val
  have hv : (mapJoinCocone F excisionGridLowerRectangleCocone).val =
      ((pastingCocone (excisionGridLowerRectangle ≫ F)).restrict
        excisionGridLowerSeedCornerIso.hom).val := by
    simp only [mapJoinCocone, excisionGridLowerRectangleCocone, JoinCocone.restrict,
      pastingCocone, Category.assoc]
  have hd := (isColimitCone_iff_of_val_eq _ _ hv).mp hc
  exact (pastingCocone_isColimitCone_iff_right _).mp
    ((isColimitCone_iff_restrict_of_isIso _ excisionGridLowerSeedCornerIso.hom).mpr hd)

lemma ExcisionGridExtension.lower_right_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    IsPushoutSquare (pastingSquare (excisionGridLowerRectangle ≫ d.core) 0) :=
  excisionGridLowerRectangle_right_pushout d.core
    (d.core_colimit (nerveVertex (excisionGridCorePoint 2 1)))

end SerrePositivity.InfinityCategories
