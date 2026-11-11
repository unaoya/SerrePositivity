module
public import SerrePositivity.KST.SConstruction.PerfectInvariantProductDecomposition

/-! # Cat^perf の半直交分解の局所化不変量値での分裂
概要：同じ実随伴の右包含を切断とし、半直交分解の不変量値の実 Sp 積分解を得る。
方針：元の射影の値の切断を実 fiber 列へ移し、同じ三射を持つ積同値に接続する。
規約：切断や積分解を入力の仮定にしない。使われ方：Tamme の lax pullback の分裂。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
variable {E : perfectStableInfinity.{u} ⟶ Sp.{u}}
  {a b t : perfectStableInfinity.{u} _⦋0⦌} (d : PerfectSemiorthogonalDecomposition a b t)

/-- 同じ半直交分解の列は、元の三つの Cat^perf 頂点を厳密に回収する。 -/
lemma perfectSemiorthogonalVerdierSequence_vertices :
    (perfectSemiorthogonalVerdierSequence d).leftVertex = a ∧
      (perfectSemiorthogonalVerdierSequence d).middleVertex = t ∧
      (perfectSemiorthogonalVerdierSequence d).rightVertex = b := by
  constructor
  · apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex_object a.val
  constructor
  · apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex_object t.val
  · apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex_object b.val

/-- 元の右包含を同じ不変量で写した、元の右値から中央値への実際の射の類。 -/
def perfectSemiorthogonalValueSection (E : perfectStableInfinity.{u} ⟶ Sp.{u}) :
    perfectInvariantHoObject E (perfectSemiorthogonalVerdierSequence d).rightVertex ⟶
      perfectInvariantHoObject E (perfectSemiorthogonalVerdierSequence d).middleVertex :=
  perfectInvariantHoArrow E d.rightInclusion (perfectStableObject_isIdempotentComplete b)
    (perfectStableObject_isIdempotentComplete t)

/-- 同じ実右包含の値は、列に用いた元の完備化後の射影の値の切断。 -/
lemma perfectSemiorthogonalValueSection_section (E : perfectStableInfinity.{u} ⟶ Sp.{u}) :
    perfectSemiorthogonalValueSection d E ≫
        perfectInvariantHoArrow E (perfectSemiorthogonalVerdierSequence d).projection
          (perfectSemiorthogonalVerdierSequence d).middle_complete
          (perfectSemiorthogonalVerdierSequence d).right_complete = 𝟙 _ := by
  have hp : (perfectSemiorthogonalVerdierSequence d).projection = d.projection :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (perfectSemiorthogonalVerdierSequence_projection d)
  change perfectInvariantHoArrow E d.rightInclusion
      (perfectStableObject_isIdempotentComplete b) (perfectStableObject_isIdempotentComplete t) ≫
    perfectInvariantHoArrow E (perfectSemiorthogonalVerdierSequence d).projection
      (perfectStableObject_isIdempotentComplete t) (perfectStableObject_isIdempotentComplete b) = _
  rw [hp]
  exact perfectSemiorthogonal_value_section E d (perfectStableObject_isIdempotentComplete b)
    (perfectStableObject_isIdempotentComplete t)

variable (hE : IsPerfectLocalizingInvariant E)

/-- 元の半直交分解の値の実 Sp 積と、元の中央の値との同値。 -/
def IsPerfectLocalizingInvariant.perfectSemiorthogonalSplitEquivalence :
    SpectrumHo.obj (NativeSplit.product
      (hE.sequenceFiberTriangle (perfectSemiorthogonalVerdierSequence d))) ≅
        perfectInvariantHoObject E (perfectSemiorthogonalVerdierSequence d).middleVertex :=
  hE.perfectSplitEquivalence (perfectSemiorthogonalVerdierSequence d)
    (perfectSemiorthogonalValueSection d E) (perfectSemiorthogonalValueSection_section d E)

/-- 同じ積分解は元の左因子の包含の値を回収する。 -/
lemma IsPerfectLocalizingInvariant.perfectSemiorthogonalSplitEquivalence_inclusion :
    SpectrumHo.hom (Binary.inl _ _) ≫ (hE.perfectSemiorthogonalSplitEquivalence d).hom =
      (hE.perfectSplitLeftFactorIso (perfectSemiorthogonalVerdierSequence d)).inv ≫
        perfectInvariantHoArrow E d.inclusion (perfectStableObject_isIdempotentComplete a)
          (perfectStableObject_isIdempotentComplete t) :=
  hE.perfectSplitEquivalence_inclusion _ _ _

/-- 同じ積分解は元の右因子の包含の値を回収する。 -/
lemma IsPerfectLocalizingInvariant.perfectSemiorthogonalSplitEquivalence_section :
    SpectrumHo.hom (Binary.inr _ _) ≫ (hE.perfectSemiorthogonalSplitEquivalence d).hom =
      (hE.perfectSplitRightFactorIso (perfectSemiorthogonalVerdierSequence d)).inv ≫
        perfectInvariantHoArrow E d.rightInclusion (perfectStableObject_isIdempotentComplete b)
          (perfectStableObject_isIdempotentComplete t) :=
  hE.perfectSplitEquivalence_section _ _ _

/-- 同じ積分解は元の射影の値を回収する。 -/
lemma IsPerfectLocalizingInvariant.perfectSemiorthogonalSplitEquivalence_projection :
    (hE.perfectSemiorthogonalSplitEquivalence d).hom ≫
        perfectInvariantHoArrow E d.projection (perfectStableObject_isIdempotentComplete t)
          (perfectStableObject_isIdempotentComplete b) =
      SpectrumHo.hom (Binary.snd _ _) ≫
        (hE.perfectSplitRightFactorIso (perfectSemiorthogonalVerdierSequence d)).inv := by
  have hp : (perfectSemiorthogonalVerdierSequence d).projection = d.projection :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (perfectSemiorthogonalVerdierSequence_projection d)
  have h := hE.perfectSplitEquivalence_projection (perfectSemiorthogonalVerdierSequence d)
    (perfectSemiorthogonalValueSection d E) (perfectSemiorthogonalValueSection_section d E)
  rw [hp] at h
  exact h

end SerrePositivity.KST.SConstruction
