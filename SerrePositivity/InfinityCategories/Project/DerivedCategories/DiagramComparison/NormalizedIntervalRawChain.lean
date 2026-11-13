module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalLowDegrees
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
/-!
概要：同じ線形化Δ[1]から任意の鎖複体への区間評価。
方針：零・一次を指定値で評価し、高次を零にする。
規約：A06の証明の分割。正規化の包含を前合成して使う。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex AlgebraicTopology
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
/-- 二頂点とその差を微分に持つ辺による、同じ標準区間の鎖写像。 -/
def intervalRawChainMap (A : Type u) [CommRing A] (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (x y : K.X 0) (w : K.X 1) (hw : K.d 1 0 w = y - x) :
    (alternatingFaceMapComplex (ModuleCat A)).obj
      ((SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj ⦋1⦌)) ⟶ K :=
  ChainComplex.ofHom (fun n => match n with
    | 0 => intervalVertexEvaluation A (K.X 0) x y
    | 1 => intervalEdgeEvaluation A (K.X 1) w
    | _ + 2 => 0) (by
      intro n
      cases n with
      | zero =>
        rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, Fin.sum_univ_two]
        simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
          Preadditive.add_comp, Preadditive.neg_comp]
        convert interval_evaluation_boundary A (K.d 1 0) x y w hw using 1 <;>
          simp only [sub_eq_add_neg, alternatingFaceMapComplex_obj_X, SimplicialObject.δ] <;> rfl
      | succ n =>
        cases n with
        | zero =>
          rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, Fin.sum_univ_three]
          simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq,
            one_zsmul, neg_one_zsmul, Preadditive.add_comp, Preadditive.neg_comp,
            CategoryTheory.Limits.zero_comp]
          simpa only [sub_eq_add_neg, alternatingFaceMapComplex_obj_X, SimplicialObject.δ] using (interval_evaluation_triangle A (K.X 1) w).symm
        | succ n =>
          simp only [CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero])
/-- 同じ区間の正規化鎖の包含を前合成した評価。 -/
def intervalNormalizedChainMap (A : Type u) [CommRing A]
    (K : ChainComplex (ModuleCat.{u} A) ℕ) (x y : K.X 0) (w : K.X 1)
    (hw : K.d 1 0 w = y - x) :
    (normalizedMooreComplex (ModuleCat A)).obj
      ((SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj ⦋1⦌)) ⟶ K :=
  inclusionOfMooreComplexMap _ ≫ intervalRawChainMap A K x y w hw

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
