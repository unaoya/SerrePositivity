module
public import SerrePositivity.DifferentialGraded.Module.ClosedMaps

/-! # 主 dg 加群 Hom end の通常射に対する関手性の成分公式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 加群射の成分を再び閉射にすると元の end 成分に戻る。 -/
lemma moduleEvaluation_closedMap (x : D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    closedMap A (P := (ForgetEnrichment.to (Complex A) M).obj (op x))
      (Q := (ForgetEnrichment.to (Complex A) N).obj (op x)) ((moduleEvaluation A D x).map f) =
    ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x :=
  closedMap_mapFromUnit A _ _ _

/-- end の後合成を評価すると通常の Hom 複体の後合成になる。 -/
@[reassoc]
lemma moduleHomWhiskerLeft_π {M N P : ModuleCategory A D} (f : N ⟶ P) (x : D) :
    eHomWhiskerLeft (Complex A) M f ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) x =
    moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x ≫
      homPostcompose ((moduleEvaluation A D x).obj M) ((moduleEvaluation A D x).map f) := by
  change (ρ_ (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N))).inv ≫
      moduleHom A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) ◁
        ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := N) (Y := P) f ≫
      moduleComposition A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) P) ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) x = _
  rw [moduleComposition_π, whiskerLeft_comp_tensorHom_assoc,
    rightUnitor_inv_comp_tensorHom_assoc, ← moduleEvaluation_closedMap,
    ← homPostcompose_closedMap]
  rfl

/-- end の前合成を評価すると通常の Hom 複体の前合成になる。 -/
@[reassoc]
lemma moduleHomWhiskerRight_π {M N P : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    eHomWhiskerRight (Complex A) f P ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) x =
    moduleHomπ A D (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) P) x ≫
      homPrecompose ((moduleEvaluation A D x).map f) ((moduleEvaluation A D x).obj P) := by
  change (λ_ (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) P))).inv ≫
      ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f ▷
        moduleHom A D (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) P) ≫
      moduleComposition A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) P) ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) x = _
  rw [moduleComposition_π, whiskerRight_comp_tensorHom_assoc,
    leftUnitor_inv_comp_tensorHom_assoc, ← moduleEvaluation_closedMap,
    ← homPrecompose_closedMap]
  rfl
/-- 加群射の通常成分の零 cochain は end 成分の閉 cycle。 -/
lemma moduleEvaluation_cochain (x : D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    Cochain.ofHom ((moduleEvaluation A D x).map f) =
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x).f 0
      (cycleFromUnit _
        (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f)).val := by
  have h := mapFromUnit_cochain A ((ForgetEnrichment.to (Complex A) M).obj (op x))
    ((ForgetEnrichment.to (Complex A) N).obj (op x))
    (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x)
  rw [cycleFromUnit_postcomp] at h
  exact h
end SerrePositivity.DifferentialGraded
