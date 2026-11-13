module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofPointSliceSimplexInverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGInitialRefinementAvoidingFaces

/-! # 任意次元の実 over 単体の閉始点細分

概要：元の回収単体を同じ閉射で始点細分し、同じ終点を固定する実 over 単体へ戻す。
方針：正の最終頂点への制限の保存で、零次元も含めて終点固定を照合する。
規約：分母条件は別に証明する。使われ方：高次境界充填の共有面と新 apex の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
variable (a : Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
  ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)).obj 0))

/-- over 単体の元の回収単体を、同じ閉射で始点細分した実単体。 -/
def dgOverSimplexInitialMap : Δ[n + 1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)) q s)

/-- 同じ閉始点細分は、元の指定終点を厳密に保つ。 -/
lemma dgOverSimplexInitialMap_fixed :
    SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n) ≫ dgOverSimplexInitialMap A D a σ q s = a := by
  unfold dgOverSimplexInitialMap
  rw [SSet.yonedaEquiv_symm_naturality_left]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_pullback_avoids_zero A D
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)) q s (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).toOrderHom
    (fun (i j : Fin 1) _ => Subsingleton.elim i j) (fun i => by
      change Fin.last (n + 1) ≠ 0
      simp)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)) q s) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)) at he
  rw [he, ← SSet.yonedaEquiv_symm_naturality_left, Equiv.symm_apply_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_fixed a σ

/-- 全次数・零次元を含む、同じ終点を固定した実 over 単体の閉始点細分。 -/
def dgOverSimplexInitialRefinement : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplexOfFixed a (dgOverSimplexInitialMap A D a σ q s)
    (dgOverSimplexInitialMap_fixed A D a σ q s)

/-- over 細分の回収単体は、元の指定回収単体の同じ閉始点細分。 -/
lemma dgOverSimplexInitialRefinement_simplex :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a (dgOverSimplexInitialRefinement A D a σ q s) =
      dgOverSimplexInitialMap A D a σ q s :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplexOfFixed_simplex a _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
