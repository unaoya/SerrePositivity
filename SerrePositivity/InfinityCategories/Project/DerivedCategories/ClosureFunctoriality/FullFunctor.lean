module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.FamilyImage
public import SerrePositivity.KST.NonConnective.DGKappaConeInput
public import SerrePositivity.DifferentialGraded.Functor.Closed

/-!
概要：実同型による像の被覆を、固定した充満部分 dg 圏間の関手へ移す。
方針：一度選んだ対象と実同型を保持し、全 Hom 複体を共役する。
規約：map_id と map_comp は dg 関手の厳密な等式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory DifferentialGraded KST.NonConnective KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (F : DGFunctor R (RightModule R C) (RightModule R D))
  (S : Set (ModuleCategory R C)) (T : Set (ModuleCategory R D))

/-- 固定した部分圏への対象作用と実比較同型。 -/
structure DGModuleStrictImage where
  obj : {M // S M} → {N // T N}
  iso : ∀ M, F.onClosed.obj M.val ≅ (obj M).val

/-- 実像の存在証明から、一回だけ選択して保持する。 -/
def DGModuleStrictImage.ofRange
    (h : ∀ M, S M → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange R D T (F.onClosed.obj M)) :
    DGModuleStrictImage R C D F S T where
  obj M := ⟨(h M.val M.property).choose, (h M.val M.property).choose_spec.1⟩
  iso M := (h M.val M.property).choose_spec.2.some.symm

variable (I : DGModuleStrictImage R C D F S T)

/-- 同じ閉同型を使い、元の延長の全次数 Hom 作用を共役する。 -/
def DGModuleStrictImage.evaluated : DGFunctor R {M // S M} (RightModule R D) :=
  dgFunctorClosedConjugate R
    (((dgFullSubcategoryInclusion R (ModuleCategory R C) S).comp
      (dgConeModuleForget R C)).comp F)
    (fun M => ForgetEnrichment.to (Complex R) (I.obj M).val) I.iso

/-- 固定代表の充満部分圏間の厳密 dg 関手。 -/
def DGModuleStrictImage.functor : DGFunctor R {M // S M} {N // T N} where
  obj := I.obj
  map := I.evaluated R C D F S T |>.map
  map_id := I.evaluated R C D F S T |>.map_id
  map_comp := I.evaluated R C D F S T |>.map_comp

/-- 全 Hom の作用は、元の作用に実比較同型の共役を合成した鎖写像。 -/
lemma DGModuleStrictImage.functor_map (M N : {M // S M}) :
    (I.functor R C D F S T).map M N =
      F.map (ForgetEnrichment.to (Complex R) M.val)
        (ForgetEnrichment.to (Complex R) N.val) ≫
          enrichedClosedIsoConjugation (Complex R) (I.iso M) (I.iso N) := by
  simp [DGModuleStrictImage.functor, DGModuleStrictImage.evaluated,
    dgFunctorClosedConjugate, dgFunctorClosedTarget, enrichedFunctorClosedConjugate,
    DGFunctor.comp, EnrichedFunctor.comp, dgFullSubcategoryInclusion, dgConeModuleForget]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
