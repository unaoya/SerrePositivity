module
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionNerve
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
/-!
概要：実入力射影に沿い、全次数の閉 cochain と境界原始元を持ち上げる。
方針：同じ次数別全射準同型を使い、shift の半自由分解と実ホモトピー逆も回収する。
規約：半自由対象が literal な shift に閉じるとは仮定しない。使われ方：全高次 Hom の検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 同じ実入力射影に沿う斉次閉射・原始元と shift 分解の比較。 -/
lemma dgModuleResolutionSource_closed_lift
    (X Y : DGModuleFunctorResolutionObject R C E F) (n : ℤ)
    (a : GradedHom R X.source Y.source n) (ha : differential R a = 0) :
    ∃ b : GradedHom R X Y n, differential R b = 0 ∧
      ((dgModuleFunctorResolutionSource R C E F).map X Y).f n b = a := by
  let z : complexCycles R (homObject R (DGModuleFunctorResolutionObject R C E F) X Y) (n + 1) :=
    ⟨0, by simp⟩
  exact complex_boundary_lifting_of_surjective_quasiIso R
    ((dgModuleFunctorResolutionSource R C E F).map X Y)
    (dgModuleFunctorResolutionSource_degree_surjective R C E F X Y)
    (dgModuleFunctorResolutionSource_homQuasiIso R C E F X Y) n z a (by
      simp only [z, map_zero]
      change (0 : GradedHom R X.source Y.source (n + 1)) = differential R a
      exact ha.symm)
/-- 同じ実入力射影に沿う斉次閉射・原始元と shift 分解の比較。 -/
lemma dgModuleResolutionSource_boundary_reflect
    (X Y : DGModuleFunctorResolutionObject R C E F) (q : ℤ)
    (a : GradedHom R X Y (q + 1)) (ha : differential R a = 0)
    (b : GradedHom R X.source Y.source q)
    (hb : differential R b = ((dgModuleFunctorResolutionSource R C E F).map X Y).f (q + 1) a) :
    ∃ h : GradedHom R X Y q, differential R h = a :=
  complexQuasiIso_boundary_reflect R ((dgModuleFunctorResolutionSource R C E F).map X Y)
    (dgModuleFunctorResolutionSource_homQuasiIso R C E F X Y) q a ha b hb

/-- 同じ実入力射影に沿う斉次閉射・原始元と shift 分解の比較。 -/
lemma dgSemifreeShift_resolution_homotopyInverse
    (D : Type v) [DGCategory R D] [Small.{u} D] (M : SemifreeDGModules R D) (s : ℤ) :
    ∃ (N : SemifreeDGModules R D)
      (π : ForgetEnrichment.of (Complex R) N.val ⟶
        ForgetEnrichment.of (Complex R) (shiftModule s M.val))
      (σ : ForgetEnrichment.of (Complex R) (shiftModule s M.val) ⟶
        ForgetEnrichment.of (Complex R) N.val),
      Nonempty (ModuleHomotopy R D (π ≫ σ) (𝟙 _)) ∧
        Nonempty (ModuleHomotopy R D (σ ≫ π) (𝟙 _)) := by
  obtain ⟨N, π, _, hq⟩ := dgSemifreeModule_resolution_exists R D (shiftModule s M.val)
  have : IsIso ((moduleToHomotopy R D).map π) :=
    moduleHomotopicallyProjective_quasiIso_isIso_homotopy R D
      (dgSemifreeModule_isProjective R D N)
      (moduleHomotopicallyProjective_shift R D (dgSemifreeModule_isProjective R D M) s) π hq
  obtain ⟨σ, hσ⟩ := (moduleToHomotopy R D).map_surjective (inv ((moduleToHomotopy R D).map π))
  refine ⟨N, π, σ, ?_, ?_⟩
  · apply (moduleToHomotopy_map_eq_iff R D _ _).mp
    rw [CategoryTheory.Functor.map_comp, hσ, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  · apply (moduleToHomotopy_map_eq_iff R D _ _).mp
    rw [CategoryTheory.Functor.map_comp, hσ, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
end SerrePositivity.InfinityCategories
