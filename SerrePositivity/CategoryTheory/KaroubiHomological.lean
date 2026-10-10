module

public import SerrePositivity.CategoryTheory.KaroubiPretriangulated
public import SerrePositivity.CategoryTheory.ExactRetract
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-! # Karoubi 包絡へのホモロジー関手の延長 -/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- 三角形の retract は、最初の三項からなる短複体の retract を与える。 -/
def shortComplexOfDistTriangleRetract {T U : Triangle C}
    (hT : T ∈ distTriang C) (hU : U ∈ distTriang C) (r : Retract T U) :
    Retract (shortComplexOfDistTriangle T hT) (shortComplexOfDistTriangle U hU) where
  i := ⟨r.i.hom₁, r.i.hom₂, r.i.hom₃, r.i.comm₁.symm, r.i.comm₂.symm⟩
  r := ⟨r.r.hom₁, r.r.hom₂, r.r.hom₃, r.r.comm₁.symm, r.r.comm₂.symm⟩
  retract := by
    apply ShortComplex.Hom.ext
    · exact congrArg TriangleMorphism.hom₁ r.retract
    · exact congrArg TriangleMorphism.hom₂ r.retract
    · exact congrArg TriangleMorphism.hom₃ r.retract

variable {A : Type*} [Category* A] [Abelian A]

/-- 元の圏でホモロジー的なら、Karoubi 包絡上でもホモロジー的である。 -/
theorem karoubi_isHomological_of_restriction (F : Karoubi C ⥤ A)
    [F.PreservesZeroMorphisms] [(toKaroubi C ⋙ F).IsHomological] : F.IsHomological where
  exact T hT := by
    have hd := hT
    obtain ⟨U, hU, ⟨r⟩⟩ := hd
    have hU' := (toKaroubi C).map_distinguished U hU
    apply shortComplex_exact_of_retract
      ((shortComplexOfDistTriangleRetract hT hU' r).map F.mapShortComplex)
    exact (toKaroubi C ⋙ F).map_distinguished_exact U hU

/-- アーベル圏を値域とするホモロジー関手の標準延長はホモロジー関手。 -/
instance karoubiExtensionToComplete_isHomological (F : C ⥤ A) [F.IsHomological] :
    ((functorExtension C A).obj F).IsHomological := by
  let e := karoubiExtensionToCompleteFactors F
  have : (toKaroubi C ⋙ (functorExtension C A).obj F).IsHomological :=
    Functor.IsHomological.of_iso e.symm
  exact karoubi_isHomological_of_restriction _

end SerrePositivity
