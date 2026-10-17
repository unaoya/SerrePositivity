module
public import SerrePositivity.DifferentialGraded.Verdier.PerfectKernelVerdier
public import SerrePositivity.DifferentialGraded.Verdier.KaroubiFunctorSquare
public import SerrePositivity.DifferentialGraded.Verdier.RetractSquare

/-! # Karoubi-first の厚い零部分圏と指定 Perf 部分圏の同定 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (S : Set D)

instance perfectNullObjectsClosedUnderIso :
    (perfectNullObjects A D S).IsClosedUnderIsomorphisms := by
  dsimp [perfectNullObjects]
  infer_instance

instance perfectNullObjectsStableUnderRetracts :
    (perfectNullObjects A D S).IsStableUnderRetracts where
  of_retract r hY :=
    (modulePerfectOver A D S).prop_of_retract (r.map (modulePerfectOver A D Set.univ).ι) hY

/-- 完備化を先に行う側の零部分圏は、実際の Perf_S の逆像と一致する。 -/
lemma karoubiNullEnvelope_eq_perfectNull :
    karoubiNullEnvelope (triaImage A D S) =
      (perfectNullObjects A D S).inverseImage (finiteCellKaroubiToPerfect A D Set.univ) := by
  let F := finiteCellKaroubiToPerfect A D Set.univ
  let N := (perfectNullObjects A D S).inverseImage F
  have : N.IsTriangulated := by dsimp [N, F]; infer_instance
  have : N.IsStableUnderRetracts :=
    ⟨fun r hY => (perfectNullObjects A D S).prop_of_retract (r.map F) hY⟩
  apply le_antisymm
  · change ((triaImage A D S).map (toKaroubi (TriaCategory A D))).triangEnvelope ≤ N
    apply (((triaImage A D S).map (toKaroubi (TriaCategory A D))).triangEnvelope_le_iff
      (Q := N)).2
    rintro X ⟨Y, hY, ⟨e⟩⟩
    apply N.prop_of_iso e
    exact (perfectNullObjects A D S).prop_of_iso
      ((triaKaroubiPerfectFactors A D).app Y).symm
      ((derivedFiniteCellOver A D S).le_retractClosure _ hY)
  · intro X hX
    obtain ⟨Y, hY, ⟨r⟩⟩ := hX
    have hYu : derivedFiniteCellOver A D Set.univ Y :=
      ObjectProperty.map_monotone
        (fun _ hM => moduleFiniteCellOver_mono A D (Set.subset_univ S) hM)
        (moduleToDerived A D) Y hY
    let Y' : TriaCategory A D := ⟨Y, hYu⟩
    let rP : Retract (F.obj X) ((triaToPerfect A D).obj Y') :=
      { i := ObjectProperty.homMk r.i
        r := ObjectProperty.homMk r.r
        retract := by apply (modulePerfectOver A D Set.univ).hom_ext; exact r.retract }
    let rK : Retract X ((toKaroubi (TriaCategory A D)).obj Y') :=
      comparisonRetractPreimage F
        (rP.trans (Retract.ofIso ((triaKaroubiPerfectFactors A D).app Y').symm))
    apply (karoubiNullEnvelope (triaImage A D S)).prop_of_retract rK
    exact ((triaImage A D S).map (toKaroubi (TriaCategory A D))).le_triangEnvelope _
      ((triaImage A D S).prop_map_obj (toKaroubi (TriaCategory A D)) hY)

lemma karoubiNullEnvelope_iff_perfect (X : Karoubi (TriaCategory A D)) :
    karoubiNullEnvelope (triaImage A D S) X ↔
      modulePerfectOver A D S ((finiteCellKaroubiToPerfect A D Set.univ).obj X).obj := by
  rw [karoubiNullEnvelope_eq_perfectNull A D S]
  rfl

/-- 零部分圏の同定は対象だけでなく、その充満部分圏の同値を与える。 -/
def perfectNullEquivalence :
    (karoubiNullEnvelope (triaImage A D S)).FullSubcategory ≌
      (perfectNullObjects A D S).FullSubcategory :=
  (finiteCellKaroubiPerfectEquivalence A D Set.univ).congrFullSubcategory
    (karoubiNullEnvelope_eq_perfectNull A D S).symm
end SerrePositivity.DifferentialGraded
