module
public import SerrePositivity.KST.SConstruction.SerreInterval

/-! # 鎖区間の元の生成元の回収と増大写像
概要：鎖区間の射の一頂点の像、射による移送、元の増大写像を構成する。
方針：disk の上の生成元の普遍性で微分を回収し、零頂点と辺で射を判定する。
規約：辺の微分は一頂点から零頂点を引く。使われ方：Serre 対角の余単位と端点保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の鎖区間の一頂点の像は、零頂点の像と辺の像の微分の和。 -/
lemma serreIntervalLift_one_cycle {K : Complex A} (z : 𝟙_ (Complex A) ⟶ K)
    (e : K.X (-1)) :
    (cycleFromUnit K (serreIntervalOne A ≫ serreIntervalLift A z e)).val =
      (cycleFromUnit K z).val + K.d (-1) 0 e := by
  have hm : serreIntervalOne A ≫ serreIntervalLift A z e =
      z + (complexSphereToDisk A (-1) ≫ (complexDiskHomEquiv A K (-1)).symm e :
        𝟙_ (Complex A) ⟶ K) := by
    simp only [serreIntervalOne, serreIntervalBoundary, serreIntervalLift, serreIntervalZero,
      Preadditive.add_comp,
      Category.assoc, biprod.inl_desc, biprod.inr_desc]
  rw [hm]
  have hd := complexSphereToDisk_comp A (-1) ((complexDiskHomEquiv A K (-1)).symm e)
  rw [Equiv.apply_symm_apply] at hd
  change (cycleFromUnit K (complexSphereToDisk A (-1) ≫
    (complexDiskHomEquiv A K (-1)).symm e)).val = K.d (-1) 0 e at hd
  change (z + _).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1) = _
  rw [HomologicalComplex.add_f_apply]
  exact congrArg (fun t => (cycleFromUnit K z).val + t) hd

/-- 元の零頂点・辺による構成は、任意の chain map に関して自然。 -/
lemma serreIntervalLift_post {K L : Complex A} (z : 𝟙_ (Complex A) ⟶ K)
    (e : K.X (-1)) (f : K ⟶ L) :
    serreIntervalLift A z e ≫ f = serreIntervalLift A (z ≫ f) (f.f (-1) e) := by
  apply serreInterval_hom_ext A
  · rw [← Category.assoc, serreIntervalLift_zero, serreIntervalLift_zero]
  · change f.f (-1) ((serreIntervalLift A z e).f (-1) (serreIntervalEdge A)) = _
    rw [serreIntervalLift_edge, serreIntervalLift_edge]

/-- 元の鎖区間の零頂点・辺を回収する射は恒等射。 -/
lemma serreIntervalLift_self :
    serreIntervalLift A (serreIntervalZero A) (serreIntervalEdge A) = 𝟙 _ := by
  apply serreInterval_hom_ext A
  · rw [serreIntervalLift_zero, Category.comp_id]
  · exact serreIntervalLift_edge A _ _

/-- 元の鎖区間の増大写像。二つの頂点を単位へ、辺を零へ写す。 -/
def serreIntervalAugmentation : serreInterval A ⟶ 𝟙_ (Complex A) :=
  serreIntervalLift A (𝟙 _) 0

/-- 増大写像は元の零頂点を単位へ写す。 -/
lemma serreIntervalAugmentation_zero :
    serreIntervalZero A ≫ serreIntervalAugmentation A = 𝟙 _ :=
  serreIntervalLift_zero A _ _

/-- 増大写像は元の辺を零へ写す。 -/
lemma serreIntervalAugmentation_edge :
    (serreIntervalAugmentation A).f (-1) (serreIntervalEdge A) = 0 :=
  serreIntervalLift_edge A _ _

/-- 増大写像は元の一頂点も単位へ写す。 -/
lemma serreIntervalAugmentation_one :
    serreIntervalOne A ≫ serreIntervalAugmentation A = 𝟙 _ := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (serreIntervalOne A ≫ serreIntervalLift A (𝟙 _) 0)).val = _
  rw [serreIntervalLift_one_cycle, map_zero, add_zero]
  rfl

end SerrePositivity.KST.SConstruction
