module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorRelativeSimplexLifting
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorBoundaryFaceCompatibility
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.BoundaryPrimitives.DGBoundaryOneExtension

/-! # dg 関手に沿う実際の相対全境界の持ち上げ

概要：全 Hom が次数ごと全射な準同型なら、正次元の全境界を目標単体の上で充填できる。
方針：実境界の面をデータへ移し、最上位を同時に持ち上げてから Yoneda 対応で戻す。
規約：対象の全射性は零次元だけに必要。使われ方：β3 の自明 Kan fibration。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

/-- 境界を表すデータから、目標を保つ実充填写像を得る。 -/
lemma dgFunctor_relative_boundary_lift_of_data (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i))
    (hq : _root_.SerrePositivity.DifferentialGraded.HomQuasiIso F) {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1))
    (he : ∀ I, I ≠ Finset.univ → s.Equation I)
    (hface : ∀ j : Fin (n + 2), s.pullback j.succAboveOrderEmb.toOrderHom =
      (SSet.yonedaEquiv (SSet.boundary.ι j ≫ b)).toSimplexData)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E (n + 1))
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F = (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm t) :
    ∃ L : (Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D,
      (∂Δ[n + 1]).ι ≫ L = b ∧ L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F = SSet.yonedaEquiv.symm t := by
  obtain ⟨u, hu, hFu⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_relative_simplex_lift F hs hq s he t
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgData_faces_map_of_relative_square F b s hface t hb)
  refine ⟨SSet.yonedaEquiv.symm u, ?_, ?_⟩
  · apply SSet.boundary.hom_ext
    intro j
    have hj : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ j u = SSet.yonedaEquiv (SSet.boundary.ι j ≫ b) := by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
      exact (hu j).trans (hface j)
    rw [← Category.assoc, SSet.boundary.ι_ι, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      hj, Equiv.symm_apply_apply]
  · apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hFu

/-- Hom 上で次数ごと全射な準同型は、全正次元の相対境界を持ち上げる。 -/
lemma dgFunctor_relative_boundary_lift (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i))
    (hq : _root_.SerrePositivity.DifferentialGraded.HomQuasiIso F) {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E (n + 1))
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F = (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm t) :
    ∃ L : (Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D,
      (∂Δ[n + 1]).ι ≫ L = b ∧ L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F = SSet.yonedaEquiv.symm t := by
  cases n with
  | zero =>
    obtain ⟨L, hL⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_boundary_one_extension b
    have hL' : (∂Δ[1]).ι ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv L) = b := by
      simpa only [Equiv.symm_apply_apply] using hL
    exact dgFunctor_relative_boundary_lift_of_data F hs hq b (SSet.yonedaEquiv L).toSimplexData
      (fun I _ => (SSet.yonedaEquiv L).equation I)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex_faces_of_boundary_extension b (SSet.yonedaEquiv L) hL') t hb
  | succ n =>
    exact dgFunctor_relative_boundary_lift_of_data F hs hq b (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBoundaryZeroData b)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBoundaryZeroData_proper_equation b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBoundaryZeroData_pullback_face b) t hb

/-- 対象上全射な dg 関手の nerve は零単体も持ち上げる。 -/
lemma dgFunctor_lift_vertex (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) (ho : Function.Surjective F.obj)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E 0) : ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 0, s.map F = t := by
  obtain ⟨x, hx⟩ := ho (t.obj 0)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  exact hx

end SerrePositivity.InfinityCategories.Project.DerivedCategories
