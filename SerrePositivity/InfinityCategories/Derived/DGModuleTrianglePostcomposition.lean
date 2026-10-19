module
public import SerrePositivity.InfinityCategories.Derived.DGModuleTriangleComponents
public import SerrePositivity.InfinityCategories.Derived.TriangleExt

/-! # dg 加群の合成三角形への後合成

概要：二辺と次数 −1 の成分を閉 dg 加群射で後合成する。
方針：全 Hom end の Leibniz 則と閉零成分の微分零を使う。
規約：全 Hom end の成分を保持。使われ方：β3 の双対比較三単体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {W X Y Z : ModuleCategory A D}
variable (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
variable (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
  (ForgetEnrichment.to (Complex A) Y) (-1))
variable (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
  (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val)
variable (q : Y ⟶ Z)

include ht

/-- 閉 dg 加群射で後合成した成分の微分。 -/
lemma dgModuleTriangle_postcompose_differential :
    (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Z)).d (-1) 0
      (compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) q)).val t
        (add_zero (-1))) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ (b ≫ q)))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (c ≫ q))).val := by
  have hq : differential (D := RightModule A D) A
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) q)).val = 0 :=
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) q)).property
  have ht' : differential (D := RightModule A D) A t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val := ht
  change differential (D := RightModule A D) A
    (compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) q)).val t
      (add_zero (-1))) = _
  rw [differential_compose, hq, zero_compose]
  simp only [Int.negOnePow_zero, one_smul, zero_add]
  rw [ht', compose_sub_right, ← dgModuleClosedCycle_comp A D (a ≫ b) q,
    ← dgModuleClosedCycle_comp A D c q, Category.assoc]

/-- 二辺とホモトピーを閉 dg 加群射で後合成した二単体。 -/
def postcomposeDGModuleTriangle : Simplex A (RightModule A D) 2 :=
  (dgModuleCompStruct A D a (b ≫ q) (c ≫ q)
    (compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) q)).val t
      (add_zero (-1))) (dgModuleTriangle_postcompose_differential A D a b c t ht q)).simplex

end SerrePositivity.InfinityCategories
