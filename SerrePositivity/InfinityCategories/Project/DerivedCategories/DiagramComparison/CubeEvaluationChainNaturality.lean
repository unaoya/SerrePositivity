module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeEvaluation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanHomChainMaps

/-!
概要：既存の立方体の旗の評価は、同じHom鎖写像による係数移送に自然。
方針：標準成分の鎖作用を各旗に適用し、有限の符号付き和の線形性を使う。
規約：IS-W2 D01の既存構成の係数移送則。計算上限は変えない。
使われ方：HA 1.3.1.16、同じcoherent比較の全HA成分と閉射の作用の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory
open SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
variable {x y : D} {x' y' : E}

/-- 標準最上位成分の評価は元のHom鎖写像と可換。 -/
theorem standardTopEval_chainMap (f : homObject R D x y ⟶ homObject R E x' y')
    (m : ℕ) (s : StandardSimplex R x y m) :
    standardTopEval x' y' m ((_root_.SerrePositivity.ComplexLimits.standardModuleChainMap f).app (Opposite.op ⦋m⦌) s) =
      f.f (-(m : ℤ)) (standardTopEval x y m s) := by
  change ((_root_.SerrePositivity.ComplexLimits.standardModuleChainMap f).app (Opposite.op ⦋m⦌) s).val.component
    Finset.univ (-(m : ℤ)) Finset.univ_nonempty (by simp) = _
  rw [_root_.SerrePositivity.ComplexLimits.standardModuleChainMap_val]
  rfl

/-- 各最大旗の同じ評価は元のHom鎖写像と可換。 -/
theorem cubeFlagEvaluation_chainMap {T : Type u} {m : ℕ} (e : Fin m ≃ T)
    (f : homObject R D x y ⟶ homObject R E x' y')
    (φ : SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶
      standardHomSpace (R := R) x y) :
    cubeFlagEvaluation e (φ ≫ Functor.whiskerRight (_root_.SerrePositivity.ComplexLimits.standardModuleChainMap f)
      (forget (ModuleCat R))) = f.f (-(m : ℤ)) (cubeFlagEvaluation e φ) := by
  exact standardTopEval_chainMap f m _

/-- 同じ立方体の符号付き旗和は元のHom鎖写像に自然。 -/
theorem cubeEvaluation_chainMap {T : Type u} {m : ℕ} (e : Fin m ≃ T)
    (f : homObject R D x y ⟶ homObject R E x' y')
    (φ : SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶
      standardHomSpace (R := R) x y) :
    cubeEvaluation e (φ ≫ Functor.whiskerRight (_root_.SerrePositivity.ComplexLimits.standardModuleChainMap f)
      (forget (ModuleCat R))) = f.f (-(m : ℤ)) (cubeEvaluation e φ) := by
  unfold cubeEvaluation
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [cubeFlagEvaluation_chainMap, map_zsmul]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
