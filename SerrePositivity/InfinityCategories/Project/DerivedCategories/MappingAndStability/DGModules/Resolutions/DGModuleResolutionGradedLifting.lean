module
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGModuleFunctorResolutionNerve
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 同じ実入力射影に沿う斉次閉射・原始元と shift 分解の比較。 -/
lemma dgModuleResolutionSource_closed_lift
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) (n : ℤ)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R X.source Y.source n) (ha : _root_.SerrePositivity.DifferentialGraded.differential R a = 0) :
    ∃ b : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y n, _root_.SerrePositivity.DifferentialGraded.differential R b = 0 ∧
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F).map X Y).f n b = a := by
  let z : complexCycles R (homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) X Y) (n + 1) :=
    ⟨0, by simp⟩
  exact _root_.SerrePositivity.DifferentialGraded.complex_boundary_lifting_of_surjective_quasiIso R
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F).map X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource_degree_surjective R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource_homQuasiIso R C E F X Y) n z a (by
      simp only [z, map_zero]
      change (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom R X.source Y.source (n + 1)) = _root_.SerrePositivity.DifferentialGraded.differential R a
      exact ha.symm)
/-- 同じ実入力射影に沿う斉次閉射・原始元と shift 分解の比較。 -/
lemma dgModuleResolutionSource_boundary_reflect
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) (q : ℤ)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y (q + 1)) (ha : _root_.SerrePositivity.DifferentialGraded.differential R a = 0)
    (b : _root_.SerrePositivity.DifferentialGraded.GradedHom R X.source Y.source q)
    (hb : differential R b = ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F).map X Y).f (q + 1) a) :
    ∃ h : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y q, _root_.SerrePositivity.DifferentialGraded.differential R h = a :=
  complexQuasiIso_boundary_reflect R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F).map X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource_homQuasiIso R C E F X Y) q a ha b hb

/-- 同じ実入力射影に沿う斉次閉射・原始元と shift 分解の比較。 -/
lemma dgSemifreeShift_resolution_homotopyInverse
    (D : Type v) [DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (s : ℤ) :
    ∃ (N : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)
      (π : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N.val ⟶
        ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M.val))
      (σ : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M.val) ⟶
        ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N.val),
      Nonempty (_root_.SerrePositivity.DifferentialGraded.ModuleHomotopy R D (π ≫ σ) (𝟙 _)) ∧
        Nonempty (_root_.SerrePositivity.DifferentialGraded.ModuleHomotopy R D (σ ≫ π) (𝟙 _)) := by
  obtain ⟨N, π, _, hq⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_resolution_exists R D (shiftModule s M.val)
  have : IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).map π) :=
    _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_quasiIso_isIso_homotopy R D
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D N)
      (moduleHomotopicallyProjective_shift R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D M) s) π hq
  obtain ⟨σ, hσ⟩ := (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).map_surjective (inv ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).map π))
  refine ⟨N, π, σ, ?_, ?_⟩
  · apply (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy_map_eq_iff R D _ _).mp
    rw [CategoryTheory.Functor.map_comp, hσ, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  · apply (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy_map_eq_iff R D _ _).mp
    rw [CategoryTheory.Functor.map_comp, hσ, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
