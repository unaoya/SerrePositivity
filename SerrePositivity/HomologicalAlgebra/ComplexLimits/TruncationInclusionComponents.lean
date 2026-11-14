module
public import SerrePositivity.EInfinity.ComplexLimits.ExtendedTruncationRestriction

/-!
概要：smart切断包含の境界外の成分を元の項同型で計算する。
方針：既存restriction比較とopposite側の切断成分則を合成する。
規約：境界条件と指定埋め込みを明記する既存構成の法則。
使われ方：HA 1.2.4、IS-W2の負次数自由鎖の成分計算。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomologicalAlgebra
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable {A : Type u} [CommRing A]

/-- 境界外では切断からrestrictionへの射は元の項同型そのもの。 -/
theorem truncLEToRestriction_nonboundary (H : Complex A)
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ)) [e.IsTruncLE]
    {n : ℕ} {i : ℤ} (hi : e.f n = i) (hn : ¬ e.BoundaryLE n) :
    (H.truncLE'ToRestriction e).f n ≫ (H.restrictionXIso e hi).hom =
      (H.truncLE'XIso e hi hn).hom := by
  have hn' : ¬ e.op.BoundaryGE n := by simpa using hn
  have h := H.op.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e.op hi hn'
  have h' := congrArg Quiver.Hom.unop h
  have hXi : (H.op.restrictionXIso e.op hi).hom.unop =
      (H.restrictionXIso e hi).inv := by
    subst i
    rfl
  change (H.truncLE'ToRestriction e).f n =
    (H.op.truncGE'XIso e.op hi hn').inv.unop ≫
      (H.op.restrictionXIso e.op hi).hom.unop at h'
  rw [h', hXi, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- 同じ延長切断包含も境界外では指定項同型になる。 -/
theorem extendedTruncationInclusion_nonboundary (H : Complex A)
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ)) [e.IsTruncLE]
    {n : ℕ} {i : ℤ} (hi : e.f n = i) (hn : ¬ e.BoundaryLE n) :
    ((H.truncLE' e).extendXIso e hi).inv ≫
      ((H.truncLEIso e).inv ≫ HomologicalComplex.ιTruncLE H e).f i =
      (H.truncLE'XIso e hi hn).hom := by
  rw [extendedTruncationInclusion_restriction, truncLEToRestriction_nonboundary H e hi hn]

end SerrePositivity.HomologicalAlgebra
