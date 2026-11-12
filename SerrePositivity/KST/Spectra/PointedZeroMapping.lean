module

public import SerrePositivity.KST.Spectra.PointedMappingParameters

/-!
概要：零対象を片側に持つ点つき写像単体集合は終対象である。
方針：基点射が同型の源では基点上の条件から写像族を決定し、終対象の標的では評価で決定する。
規約：Kan 性は不要。使われ方：Sp の零対象の豊穣な普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
namespace SerrePositivity.KST.Spectra.PointedZeroMapping

/-- 基点射が同型である点つき対象からの任意の射は零射。 -/
lemma hom_eq_zero (Z Y : PointedSimplicialSet.{u}) [IsIso Z.hom] (f : Z ⟶ Y) : f = 0 := by
  apply Under.UnderMorphism.ext
  apply (cancel_epi Z.hom).mp
  exact (Under.w f).trans (Under.w (0 : Z ⟶ Y)).symm

/-- 源の基点射が同型なら、任意のパラメータを持つ点つき写像族は一意。 -/
lemma source_hom_ext (Z Y : PointedSimplicialSet.{u}) [IsIso Z.hom]
    {A : SSet.{u}} (f g : A ⟶ (PointedObject.basedHom Z Y).right) : f = g := by
  apply (cancel_mono (PointedObject.basedHomι Z Y)).mp
  apply MonoidalClosed.uncurry_injective
  apply (cancel_epi (Z.hom ▷ A)).mp
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint]

/-- 零対象からの点つき写像単体集合は終対象。 -/
def source_isTerminal (Z Y : PointedSimplicialSet.{u}) [IsIso Z.hom] :
    IsTerminal (PointedObject.basedHom Z Y).right :=
  IsTerminal.ofUniqueHom (fun A ↦ toUnit A ≫ (PointedObject.basedHom Z Y).hom)
    (fun _ _ ↦ source_hom_ext Z Y _ _)

/-- 標的が終対象なら、任意のパラメータを持つ点つき写像族は一意。 -/
lemma target_hom_ext (X Z : PointedSimplicialSet.{u}) (hZ : IsTerminal Z.right)
    {A : SSet.{u}} (f g : A ⟶ (PointedObject.basedHom X Z).right) : f = g := by
  apply (cancel_mono (PointedObject.basedHomι X Z)).mp
  apply MonoidalClosed.uncurry_injective
  exact hZ.hom_ext _ _

/-- 零対象への点つき写像単体集合は終対象。 -/
def target_isTerminal (X Z : PointedSimplicialSet.{u}) (hZ : IsTerminal Z.right) :
    IsTerminal (PointedObject.basedHom X Z).right :=
  IsTerminal.ofUniqueHom (fun A ↦ toUnit A ≫ (PointedObject.basedHom X Z).hom)
    (fun _ _ ↦ target_hom_ext X Z hZ _ _)

end SerrePositivity.KST.Spectra.PointedZeroMapping
