import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe w v uD vD u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

section GeneralOriginalUniverse
variable {D : Type uD} [Category.{vD} D] (K F : D ⥤ SSet.{v})
  (a : NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K) F)
-- The entire parameter and every chain degree remain in SSet v, independently of index sizes.
example {n : ℕ} (c : ComposableArrows D n) :
    K.obj (c.obj 0) ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      F.obj (c.obj (Fin.last n)) := NerveSmallFamilies.family K F a c
example {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    K.obj (c.obj 0) ◁ SSet.stdSimplex.map θ ≫ NerveSmallFamilies.family K F a c =
      ((K.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0))))) ▷
        SSet.stdSimplex.obj (SimplexCategory.mk m) ≫ NerveSmallFamilies.family K F a
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
      F.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) :=
  NerveSmallFamilies.family_naturality K F a c θ
end GeneralOriginalUniverse

section ActualSmallMixedActions
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
open ResolutionMixedDiagram ResolutionMixedSmallFamilies ResolutionMixedSmallAction

example (side : Bool) (p : Index C) : NerveSmallFamilies.point (smallParameter C)
    (smallValues C) (system C hcof hfib side) p =
    RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
      (ResolutionMixedTriangles.oldBoundary C p)
      (ResolutionMixedTriangles.oldTriangle C hcof hfib p side) :=
  point_recover C hcof hfib side p
example (side : Bool) (k : Fin 3) {n : ℕ} (c : ComposableArrows (Index C) n) :
    faceFamily C hcof hfib side k c =
      ((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫
        family C hcof hfib side c := family_face C hcof hfib side k c
example (side : Bool) (k : Fin 3) {n : ℕ} (c : ComposableArrows (Index C) n) (Z : C)
    (t : chainParameter C c ⟶ input C (c.obj (Fin.last n)) Z) :
    ((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫
      action C hcof hfib side c Z t = faceAction C hcof hfib side k c Z
      (((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ t) :=
  action_face C hcof hfib side k c Z t
example (side : Bool) {n : ℕ} (c : ComposableArrows (Index C) n) {Z Z' : C} (h : Z ⟶ Z')
    (t : chainParameter C c ⟶ input C (c.obj (Fin.last n)) Z) :
    action C hcof hfib side c Z' (t ≫ (cosimplicialHom
      (c.obj (Fin.last n)).final.resolution.obj).map h) = action C hcof hfib side c Z t ≫
      (KanLiftAction.targetFunctor hcof hfib (c.obj (Fin.last n)).source.inner).map h :=
  action_target_naturality C hcof hfib side c h t
example {n : ℕ} (c : ComposableArrows (Index C) n) (Z : C)
    (t : faceParameter C c ⟶ input C (c.obj (Fin.last n)) Z) :
    faceAction C hcof hfib true 1 c Z t = faceAction C hcof hfib false 1 c Z t :=
  ResolutionMixedSmallAction.shared_diagonal C hcof hfib c Z t
example (p : Index C) (Z : C) : SSet.KanComplex (output C hcof hfib p Z) :=
  output_kanComplex C hcof hfib p Z
example (side : Bool) (p : Index C) (Z : C)
    (t : (smallParameter C).obj p ⟶ input C p Z) :
    KanLiftAction.parameterized hcof hfib p.source.inner p.final (total C p) Z
      (NerveSmallFamilies.point (smallParameter C) (smallValues C) (system C hcof hfib side) p) t =
    KanLiftAction.parameterized hcof hfib p.source.inner p.final (total C p) Z
      (RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
        (ResolutionMixedTriangles.oldBoundary C p)
        (ResolutionMixedTriangles.oldTriangle C hcof hfib p side)) t :=
  point_action_recover C hcof hfib side p Z t
end ActualSmallMixedActions

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveSmallFamilies,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftProductParameter,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedSmallFamilies,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedSmallAction]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do
    throwError "Some small mixed action modules were not audited"
  logInfo m!"Small mixed action audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
