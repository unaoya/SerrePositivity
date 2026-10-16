module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies

/-! # The whole coherent mixed triangles act on the original small resolution Hom spaces -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedSmallFamilies

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedSmallAction
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev input (p : Index C) (Z : C) := (cosimplicialHom p.final.resolution.obj).obj Z
abbrev output (p : Index C) (Z : C) := KanLiftAction.target hcof hfib p.source.inner Z
abbrev total (p : Index C) := p.pre.map.base ≫ p.center ≫ p.post.base
abbrev chainParameter {n : ℕ} (c : ComposableArrows (Index C) n) :=
  (smallParameter C).obj (c.obj 0) ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n)
abbrev faceParameter {n : ℕ} (c : ComposableArrows (Index C) n) :=
  (smallIntervalParameter C).obj (c.obj 0) ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n)

/-- No parameters or action values are moved to a larger simplicial universe. -/
def action (side : Bool) {n : ℕ} (c : ComposableArrows (Index C) n) (Z : C)
    (t : chainParameter C c ⟶ input C (c.obj (Fin.last n)) Z) :
    chainParameter C c ⟶ output C hcof hfib (c.obj (Fin.last n)) Z :=
  KanLiftAction.parameterized hcof hfib (c.obj (Fin.last n)).source.inner
    (c.obj (Fin.last n)).final (total C (c.obj (Fin.last n))) Z (family C hcof hfib side c) t

def faceAction (side : Bool) (k : Fin 3) {n : ℕ} (c : ComposableArrows (Index C) n) (Z : C)
    (t : faceParameter C c ⟶ input C (c.obj (Fin.last n)) Z) :
    faceParameter C c ⟶ output C hcof hfib (c.obj (Fin.last n)) Z :=
  KanLiftAction.parameterized hcof hfib (c.obj (Fin.last n)).source.inner
    (c.obj (Fin.last n)).final (total C (c.obj (Fin.last n))) Z
      (faceFamily C hcof hfib side k c) t

lemma action_face (side : Bool) (k : Fin 3) {n : ℕ} (c : ComposableArrows (Index C) n) (Z : C)
    (t : chainParameter C c ⟶ input C (c.obj (Fin.last n)) Z) :
    ((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫
      action C hcof hfib side c Z t =
    faceAction C hcof hfib side k c Z
      (((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ t) := by
  change _ ≫ KanLiftAction.parameterized _ _ _ _ _ _ _ _ = _
  rw [KanLiftAction.parameterized_naturality, ← family_face]
  rfl

lemma action_target_naturality (side : Bool) {n : ℕ} (c : ComposableArrows (Index C) n)
    {Z Z' : C} (h : Z ⟶ Z') (t : chainParameter C c ⟶ input C (c.obj (Fin.last n)) Z) :
    action C hcof hfib side c Z' (t ≫ (cosimplicialHom
      (c.obj (Fin.last n)).final.resolution.obj).map h) =
    action C hcof hfib side c Z t ≫
      (KanLiftAction.targetFunctor hcof hfib (c.obj (Fin.last n)).source.inner).map h :=
  KanLiftAction.parameterized_target_naturality _ _ _ _ _ h _ _

lemma shared_diagonal {n : ℕ} (c : ComposableArrows (Index C) n) (Z : C)
    (t : faceParameter C c ⟶ input C (c.obj (Fin.last n)) Z) :
    faceAction C hcof hfib true 1 c Z t = faceAction C hcof hfib false 1 c Z t :=
  congrArg (fun s => KanLiftAction.parameterized hcof hfib (c.obj (Fin.last n)).source.inner
    (c.obj (Fin.last n)).final (total C (c.obj (Fin.last n))) Z s t)
    (ResolutionMixedSmallFamilies.shared_diagonal C hcof hfib c)

lemma output_kanComplex (p : Index C) (Z : C) : SSet.KanComplex (output C hcof hfib p Z) :=
  KanLiftAction.target_kanComplex _ _ _ _

/-- At each original presentation the action uses exactly the old whole small triangle family. -/
lemma point_action_recover (side : Bool) (p : Index C) (Z : C)
    (t : (smallParameter C).obj p ⟶ input C p Z) :
    KanLiftAction.parameterized hcof hfib p.source.inner p.final (total C p) Z
      (NerveSmallFamilies.point (smallParameter C) (smallValues C) (system C hcof hfib side) p) t =
    KanLiftAction.parameterized hcof hfib p.source.inner p.final (total C p) Z
      (RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
        (ResolutionMixedTriangles.oldBoundary C p)
        (ResolutionMixedTriangles.oldTriangle C hcof hfib p side)) t :=
  congrArg (fun s => KanLiftAction.parameterized hcof hfib p.source.inner p.final
    (total C p) Z s t) (point_recover C hcof hfib side p)

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedSmallAction
