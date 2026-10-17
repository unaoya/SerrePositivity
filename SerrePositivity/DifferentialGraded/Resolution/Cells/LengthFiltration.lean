module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.LengthBoundary

/-! # path長上限で切った最終Hom複体とその包含 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

lemma lengthReplacement_closed (n : ℕ) (x y : D) :
    δ 1 2 (C.lengthReplacement A D I n x y) = 0 :=
  perturbation_closed_of_inclusion (C.lengthInclusion A D I n x y)
    (C.lengthProjection A D I n x y) (C.lengthInclusion_projection A D I n x y)
    (C.lengthReplacement A D I n x y) (C.replacement A D I x y)
    (C.replacement_closed A D I x y) (C.lengthReplacement_inclusion A D I n x y)

lemma lengthReplacement_square_zero (n : ℕ) (x y : D) :
    (C.lengthReplacement A D I n x y).comp (C.lengthReplacement A D I n x y)
      (show (1 : ℤ) + 1 = 2 by omega) = 0 :=
  perturbation_square_zero_of_inclusion (C.lengthInclusion A D I n x y)
    (C.lengthProjection A D I n x y) (C.lengthInclusion_projection A D I n x y)
    (C.lengthReplacement A D I n x y) (C.replacement A D I x y)
    (C.replacement_square_zero A D I x y) (C.lengthReplacement_inclusion A D I n x y)

/-- 内部微分だけでなく、指定境界置換を含む長さn以下のpath複体。 -/
def lengthHom (n : ℕ) (x y : D) : Complex A :=
  perturbComplex (C.lengthInternalHom A D I n x y) (C.lengthReplacement A D I n x y)
    (C.lengthReplacement_closed A D I n x y) (C.lengthReplacement_square_zero A D I n x y)

lemma lengthHom_d (n : ℕ) (x y : D) (i : ℤ) :
    (C.lengthHom A D I n x y).d i (i + 1) =
    (C.lengthInternalHom A D I n x y).d i (i + 1) +
      (C.lengthReplacement A D I n x y).v i (i + 1) rfl :=
  perturbComplex_d _ _ _ _ _

def lengthHomInclusion (n : ℕ) (x y : D) :
    C.lengthHom A D I n x y ⟶ C.attachedHom A D I x y :=
  perturbMap (C.lengthInclusion A D I n x y)
    (C.lengthReplacement A D I n x y) (C.replacement A D I x y)
    (C.lengthReplacement_closed A D I n x y) (C.replacement_closed A D I x y)
    (C.lengthReplacement_square_zero A D I n x y) (C.replacement_square_zero A D I x y)
    (C.lengthReplacement_inclusion A D I n x y)

lemma lengthHomInclusion_f (n : ℕ) (x y : D) (i : ℤ) :
    (C.lengthHomInclusion A D I n x y).f i = (C.lengthInclusion A D I n x y).f i := rfl

instance lengthHomInclusion_degreewiseMono (n : ℕ) (x y : D) (i : ℤ) :
    Mono ((C.lengthHomInclusion A D I n x y).f i) := by
  let : IsSplitMono ((C.lengthHomInclusion A D I n x y).f i) :=
    ⟨⟨{ retraction := (C.lengthProjection A D I n x y).f i, id := by
           change (C.lengthInclusion A D I n x y).f i ≫
             (C.lengthProjection A D I n x y).f i =
             𝟙 ((C.lengthInternalHom A D I n x y).X i)
           simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
             congrArg (fun f => f.f i) (C.lengthInclusion_projection A D I n x y) }⟩⟩
  infer_instance

instance lengthHomInclusion_mono (n : ℕ) (x y : D) :
    Mono (C.lengthHomInclusion A D I n x y) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  infer_instance

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
