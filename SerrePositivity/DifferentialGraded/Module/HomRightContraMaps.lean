module
public import SerrePositivity.DifferentialGraded.Module.HomRightContra
public import SerrePositivity.DifferentialGraded.Complexes.HomContravariantMaps

/-! # 左加群変数の反変Hom写像と閉零射の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma leftModuleEvaluation_closedMap (x : D) {N N' : LeftModuleCategory A D} (f : N ⟶ N') :
    closedMap A ((leftModuleEvaluation A D x).map f) =
    ForgetEnrichment.homTo (Complex A) (C := LeftModule A D) f ≫
      leftModuleHomπ A D (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) N') x :=
  closedMap_mapFromUnit A _ _ _

lemma homRightContraHomMap_closed_component {N N' : LeftModuleCategory A D} (f : N ⟶ N')
    (T : Complex A) (x : D) :
    (ForgetEnrichment.homTo (Complex A) (C := LeftModule A D) f ≫
      homRightContraHomMap A D (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) N') T) ≫
      moduleHomπ A D (homRightModule A D (ForgetEnrichment.to (Complex A) N') T)
        (homRightModule A D (ForgetEnrichment.to (Complex A) N) T) x =
      closedMap A (homPrecompose ((leftModuleEvaluation A D x).map f) T) := by
  rw [Category.assoc, homRightContraHomMap_π]
  change (ForgetEnrichment.homTo (Complex A) (C := LeftModule A D) f ≫
      leftModuleHomπ A D (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) N') x) ≫
      (homContravariantDG A T).map
        (op ((ForgetEnrichment.to (Complex A) N').obj x))
        (op ((ForgetEnrichment.to (Complex A) N).obj x)) = _
  have h := congrArg (fun t => t ≫ (homContravariantDG A T).map
      (op ((ForgetEnrichment.to (Complex A) N').obj x))
      (op ((ForgetEnrichment.to (Complex A) N).obj x))) (leftModuleEvaluation_closedMap A D x f)
  exact h.symm.trans (homContravariantDG_closedMap A ((leftModuleEvaluation A D x).map f) T)

/-- 豊穣oppositeと閉零圏のoppositeの既存比較を介した反変右Hom関手。 -/
def homRightContraFunctor (T : Complex A) : (LeftModuleCategory A D)ᵒᵖ ⥤ ModuleCategory A D :=
  (forgetEnrichmentOppositeEquivalence (Complex A) (LeftModule A D)).inverse ⋙
    (homRightContraDG A D T).onClosed

@[simp]
lemma homRightContraFunctor_map_eval {N N' : LeftModuleCategory A D} (f : N ⟶ N')
    (T : Complex A) (x : D) :
    (moduleEvaluation A D x).map ((homRightContraFunctor A D T).map f.op) =
      homPrecompose ((leftModuleEvaluation A D x).map f) T := by
  have h := congrArg (mapFromUnit A _ _) (homRightContraHomMap_closed_component A D f T x)
  rw [mapFromUnit_closedMap] at h
  exact h

end SerrePositivity.DifferentialGraded
