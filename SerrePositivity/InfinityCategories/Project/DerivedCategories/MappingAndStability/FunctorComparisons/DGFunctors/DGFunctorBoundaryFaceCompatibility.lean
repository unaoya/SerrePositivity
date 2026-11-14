module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.BoundaryPrimitives.DGBoundaryAssembly
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor

/-! # 相対境界の面と dg 関手の像の両立

概要：境界を dg 関手で写した式を、単体データの全面の式へ移す。
方針：Yoneda 対応と面包含の合成を用い、最後にデータ部分を取る。
規約：全正次元で成立する。使われ方：β3 の相対全境界持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [DGCategory A E]

/-- 実境界の延長式から、充填単体の全ての面の式を得る。 -/
lemma dgSimplex_faces_of_boundary_extension {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (u : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (n + 1))
    (hb : (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm u = b) (j : Fin (n + 2)) :
    u.toSimplexData.pullback j.succAboveOrderEmb.toOrderHom =
      (SSet.yonedaEquiv (SSet.boundary.ι j ≫ b)).toSimplexData := by
  have he := congrArg (fun G : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D =>
    SSet.yonedaEquiv (SSet.boundary.ι j ≫ G)) hb
  rw [← Category.assoc, SSet.boundary.ι_ι, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
    Equiv.apply_symm_apply] at he
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData he

/-- dg 関手で写した境界の面は、目標単体の対応する面となる。 -/
lemma dgBoundaryFace_map_of_relative_square {n : ℕ} (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E (n + 1))
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F = (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm t)
    (j : Fin (n + 2)) :
    (SSet.yonedaEquiv (SSet.boundary.ι j ≫ b)).map F = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E).δ j t := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F).app _ (SSet.yonedaEquiv (SSet.boundary.ι j ≫ b)) = _
  rw [← SSet.yonedaEquiv_comp, Category.assoc, hb, ← Category.assoc,
    SSet.boundary.ι_ι, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply]

/-- 境界から得た源のデータの全面は、写した後に目標の全面と一致する。 -/
lemma dgData_faces_map_of_relative_square {n : ℕ} (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1))
    (hs : ∀ j : Fin (n + 2), s.pullback j.succAboveOrderEmb.toOrderHom =
      (SSet.yonedaEquiv (SSet.boundary.ι j ≫ b)).toSimplexData)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E (n + 1))
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F = (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm t)
    (j : Fin (n + 2)) :
    (s.map F).pullback j.succAboveOrderEmb.toOrderHom =
      t.toSimplexData.pullback j.succAboveOrderEmb.toOrderHom := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map_pullback, hs j]
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData (dgBoundaryFace_map_of_relative_square F b t hb j)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
