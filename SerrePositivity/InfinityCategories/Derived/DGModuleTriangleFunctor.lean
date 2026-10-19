module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorClosedCycles
public import SerrePositivity.InfinityCategories.Derived.DGModuleTrianglePostcomposition
public import SerrePositivity.InfinityCategories.DGNerve.Functor

/-! # dg 関手による実加群三角形の保存

概要：合成の差の原始元と実二単体を dg 関手で同時に送る。
方針：Hom の chain map と閉零 cycle の比較で微分式を移し、全四成分を照合する。
規約：Hom end の次数 −1 成分を厳密に保持。使われ方：実四角形の関手像。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
variable (F : DGFunctor A (RightModule A D) (RightModule A E))
variable {W X Y : ModuleCategory A D} (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
variable (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
  (ForgetEnrichment.to (Complex A) Y) (-1))
variable (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
  (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val)

include ht

/-- 原始元の像の微分は実閉零射の像の合成の差。 -/
lemma dgModuleTriangle_map_differential :
    (moduleHom A E (F.obj (ForgetEnrichment.to (Complex A) W))
      (F.obj (ForgetEnrichment.to (Complex A) Y))).d (-1) 0
        ((F.map (ForgetEnrichment.to (Complex A) W)
          (ForgetEnrichment.to (Complex A) Y)).f (-1) t) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (F.onClosed.map a ≫ F.onClosed.map b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (F.onClosed.map c))).val := by
  have h := ConcreteCategory.congr_hom
    ((F.map (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y)).comm (-1) 0) t
  change _ = (F.map (ForgetEnrichment.to (Complex A) W)
    (ForgetEnrichment.to (Complex A) Y)).f 0
      ((moduleHom A D (ForgetEnrichment.to (Complex A) W)
        (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t) at h
  rw [ht, map_sub, dgFunctor_mapClosedCycle, dgFunctor_mapClosedCycle, Functor.map_comp] at h
  exact h

/-- 実三角形の全対象・辺・次数 −1 成分は dg 関手の像と一致する。 -/
lemma dgModuleCompStruct_map :
    (dgModuleCompStruct A D a b c t ht).simplex.map F =
      (dgModuleCompStruct A E (F.onClosed.map a) (F.onClosed.map b) (F.onClosed.map c)
        ((F.map (ForgetEnrichment.to (Complex A) W)
          (ForgetEnrichment.to (Complex A) Y)).f (-1) t)
        (dgModuleTriangle_map_differential A D E F a b c t ht)).simplex := by
  apply dgSimplex2_ext
  · funext i
    fin_cases i <;> rfl
  · exact heq_of_eq (dgFunctor_mapClosedCycle F a)
  · exact heq_of_eq (dgFunctor_mapClosedCycle F b)
  · exact heq_of_eq (dgFunctor_mapClosedCycle F c)
  · rfl

end SerrePositivity.InfinityCategories
