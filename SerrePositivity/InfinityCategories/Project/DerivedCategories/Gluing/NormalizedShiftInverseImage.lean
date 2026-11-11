module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizedShiftUnits

/-! 標準シフトの逆斉次元の dg 関手像を、同じ正規化シフト同型の逆射と同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (C : Type w) [DGCategory R C] [Small.{u} C]
  (F : DGFunctor R (RightModule R D) (RightModule R C))
  (n : ℤ) (U : RightModule R D) (c : C) (i : ℤ)

/-- 同じ次数 −n の逆元の評価は、正規化したシフト比較の逆射の評価。 -/
lemma dgGluingNormalizedShiftInImage_v :
    (((moduleHomπ R C (F.obj U) (F.obj (shiftModule n U)) c).f (-n)
      ((F.map U (shiftModule n U)).f (-n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizedShiftIn R D n U))).v
        (i + n) i (by omega)) =
      ((moduleEvaluation R C c).map (normalizedDGModuleFunctorShiftIso R D C F n U).inv).f i := by
  let H := F.comp (moduleEvaluationDG R C c)
  have h := congrArg (fun z => (H.map (shiftModule n U) (shiftModule n U)).f 0 z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizedShiftOutIn R D n U)
  rw [H.map_compose_cochain R, H.map_unitElement R, Bimodule.complex_unitElement] at h
  have hv := Cochain.congr_v h i i (add_zero i)
  rw [Cochain.comp_v _ _ _ i (i + n) i rfl (by omega), Cochain.ofHom_v, id_f] at hv
  change (((moduleHomπ R C (F.obj (shiftModule n U)) (F.obj U) c).f n
      ((F.map (shiftModule n U) U).f n (normalizedModuleShiftOut R D n U))).v
        i (i + n) rfl) ≫
    (((moduleHomπ R C (F.obj U) (F.obj (shiftModule n U)) c).f (-n)
      ((F.map U (shiftModule n U)).f (-n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizedShiftIn R D n U))).v
        (i + n) i (by omega)) = 𝟙 _ at hv
  rw [← normalizedDGModuleFunctorShiftIso_hom_eval_f] at hv
  have hi := congrArg (fun f => ((moduleEvaluation R C c).map f).f i)
    (normalizedDGModuleFunctorShiftIso R D C F n U).hom_inv_id
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    HomologicalComplex.comp_f, HomologicalComplex.id_f] at hi
  exact (cancel_epi
    (((moduleEvaluation R C c).map
      (normalizedDGModuleFunctorShiftIso R D C F n U).hom).f i)).1 (hv.trans hi.symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
