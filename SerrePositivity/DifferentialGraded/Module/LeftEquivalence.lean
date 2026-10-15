module
public import SerrePositivity.DifferentialGraded.Module.LeftCategory
public import Mathlib.CategoryTheory.Equivalence
public import SerrePositivity.DifferentialGraded.Complexes.ClosedMaps

/-! # 左加群閉零圏とopposite上の右加群閉零圏の同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既存比較のHom写像は主Hom end上の恒等写像。 -/
def leftModuleToRightOppositeFullyFaithful : (leftModuleToRightOpposite A D).FullyFaithful where
  preimage f := f
  map_preimage {X Y} f := by
    let H : Complex A := leftModuleHom A D (ForgetEnrichment.to (Complex A) X)
      (ForgetEnrichment.to (Complex A) Y)
    change ForgetEnrichment.homTo (Complex A) (C := RightModule A Dᵒᵖ) f ≫ 𝟙 H =
      ForgetEnrichment.homTo (Complex A) (C := RightModule A Dᵒᵖ) f
    exact Category.comp_id _
  preimage_map {X Y} f := by
    let H : Complex A := leftModuleHom A D (ForgetEnrichment.to (Complex A) X)
      (ForgetEnrichment.to (Complex A) Y)
    change ForgetEnrichment.homTo (Complex A) (C := LeftModule A D) f ≫ 𝟙 H =
      ForgetEnrichment.homTo (Complex A) (C := LeftModule A D) f
    exact Category.comp_id _

instance leftModuleToRightOppositeEssSurj : (leftModuleToRightOpposite A D).EssSurj where
  mem_essImage R := by
    refine ⟨ForgetEnrichment.of (Complex A)
      (LeftModule.ofRightOpposite (ForgetEnrichment.to (Complex A) R)), ⟨?_⟩⟩
    exact eqToIso (congrArg (ForgetEnrichment.of (Complex A))
      (LeftModule.to_ofRightOpposite (ForgetEnrichment.to (Complex A) R)))

instance leftModuleToRightOppositeIsEquivalence :
    (leftModuleToRightOpposite A D).IsEquivalence where
  faithful := (leftModuleToRightOppositeFullyFaithful A D).faithful
  full := (leftModuleToRightOppositeFullyFaithful A D).full

/-- 対象データだけでなく、全Hom endの閉零射を持つ圏の同値。 -/
def leftRightOppositeEquivalence : LeftModuleCategory A D ≌ ModuleCategory A Dᵒᵖ :=
  (leftModuleToRightOpposite A D).asEquivalence

@[simp]
lemma leftModuleToRightOpposite_map_eval {N N' : LeftModuleCategory A D} (f : N ⟶ N') (x : D) :
    (moduleEvaluation A Dᵒᵖ (op x)).map ((leftModuleToRightOpposite A D).map f) =
      (leftModuleEvaluation A D x).map f := by
  change mapFromUnit A _ _ ((ForgetEnrichment.homTo (Complex A) f ≫ 𝟙 _) ≫
      moduleHomπ A Dᵒᵖ (ForgetEnrichment.to (Complex A) N).toRightOpposite
        (ForgetEnrichment.to (Complex A) N').toRightOpposite (op x)) =
    mapFromUnit A _ _ (ForgetEnrichment.homTo (Complex A) f ≫
      moduleHomπ A Dᵒᵖ (ForgetEnrichment.to (Complex A) N).toRightOpposite
        (ForgetEnrichment.to (Complex A) N').toRightOpposite (op x))
  rw [Category.comp_id]

end SerrePositivity.DifferentialGraded
