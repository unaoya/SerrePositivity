module
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Complexes.Cone

/-! 加群の互いに逆な閉斉次元から、全 dg 自然な実シフト同型を構成する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (U V : RightModule R D) (n : ℤ)
  (a : (moduleHom R D U V).X n) (b : (moduleHom R D V U).X (-n))
  (ha : (moduleHom R D U V).d n (n + 1) a = 0)
  (hab : compose R b a (add_neg_cancel n) = (unitElement R U).val)
  (hba : compose R a b (neg_add_cancel n) = (unitElement R V).val)

include ha in
lemma dgGluingModuleShiftElement_closed (x : D) :
    δ n (n + 1) ((moduleHomπ R D U V x).f n a) = 0 := by
  rw [← moduleHomElement_d_π, ha, map_zero]

include hab in
lemma dgGluingModuleShiftElement_out_in (x : D) :
    ((moduleHomπ R D U V x).f n a).comp ((moduleHomπ R D V U x).f (-n) b)
      (add_neg_cancel n) = Cochain.ofHom (𝟙 (U.obj (op x))) := by
  have h := congrArg (fun z => (moduleHomπ R D U U x).f 0 z) hab
  rw [moduleHomCompose_π, yoneda_moduleUnit_π] at h
  exact h

include hba in
lemma dgGluingModuleShiftElement_in_out (x : D) :
    ((moduleHomπ R D V U x).f (-n) b).comp ((moduleHomπ R D U V x).f n a)
      (neg_add_cancel n) = Cochain.ofHom (𝟙 (V.obj (op x))) := by
  have h := congrArg (fun z => (moduleHomπ R D V V x).f 0 z) hba
  rw [moduleHomCompose_π, yoneda_moduleUnit_π] at h
  exact h

/-- 同じ閉斉次元を順射の評価に保つ、加群の実シフト同型。 -/
def dgGluingModuleShiftGradedIso :
    ForgetEnrichment.of (Complex R) U ≅ ForgetEnrichment.of (Complex R) (shiftModule n V) :=
  moduleIsoMk R D
    (fun x => complexShiftIso R ((moduleHomπ R D U V x.unop).f n a)
      (dgGluingModuleShiftElement_closed R D U V n a ha x.unop)
      ((moduleHomπ R D V U x.unop).f (-n) b)
      (dgGluingModuleShiftElement_out_in R D U V n a b hab x.unop)
      (dgGluingModuleShiftElement_in_out R D U V n a b hba x.unop))
    (by
      apply moduleShiftRepresentation_naturality R D n a
      intro x i
      exact complexShiftComparison_f R _ _ i)

lemma dgGluingModuleShiftGradedIso_hom_eval_f (x : D) (i : ℤ) :
    ((moduleEvaluation R D x).map
      (dgGluingModuleShiftGradedIso R D U V n a b ha hab hba).hom).f i =
      ((moduleHomπ R D U V x).f n a).v i (i + n) rfl := by
  rw [dgGluingModuleShiftGradedIso, moduleIsoMk_hom_eval]
  exact complexShiftComparison_f R _ _ i

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
