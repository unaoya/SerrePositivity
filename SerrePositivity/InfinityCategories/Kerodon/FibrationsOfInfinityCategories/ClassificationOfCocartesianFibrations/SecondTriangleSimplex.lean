module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SecondTrianglePureHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SecondTriangleLastHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SecondTriangleTargetHom

/-!
概要：元の第二三角形の全単体は、同じ零成分と終域輸送の標準合成図式そのもの。
方針：三対象と六つの順方向 Hom の一致を、豊穣関手の外延性で束ねる。
規約：元の全 Hom の全次数を保持し、固定成分の仮定は使わない。
使われ方：元の固定成分比較と標準対角 fiber 比較の厳密な一致。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の第二三角形の切断単体は、同じ標準合成三角形の切断単体と一致する。 -/
lemma cocartesianSecondTriangleCutSimplex_eq_canonical
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex F G a s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCanonicalSimplex F G a s := by
  apply EnrichedFunctor.ext SSet (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj F G a s i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  by_cases hij : i ≤ j
  · generalize hi : (stdSimplex.objEquiv a) i = k
    generalize hj : (stdSimplex.objEquiv a) j = l
    have hkl : k ≤ l := by
      rw [← hi, ← hj]
      exact (stdSimplex.objEquiv a).toOrderHom.monotone hij
    fin_cases k <;> fin_cases l
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_eq_of_normalized _ _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj F G a s i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj F G a s j)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj_zero F G a s i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj_zero F G a s j hj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCanonicalSimplex_obj_zero F G a s i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCanonicalSimplex_obj_zero F G a s j hj)
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_zeroHom F G a s i j hij hi hj).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex_zeroHom _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_support a)
          i j (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_zero a i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_zero a j hj)).symm
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_zero_middle F G a s i j hij hi hj
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_zero_last F G a s i j hij hi hj
    · exact False.elim ((by decide : ¬ (1 : Fin 3) ≤ 0) hkl)
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_eq_of_normalized _ _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj F G a s i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj F G a s j)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj_middle F G a s i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj_middle F G a s j hj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCanonicalSimplex_obj_middle F G a s i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCanonicalSimplex_obj_middle F G a s j hj)
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_middleHom F G a s i j hij hi hj).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex_middleHom _ _ _ _ i j
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime_zero a i 1 hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime_zero a j 1 hj)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_one a i 0 hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_one a j 0 hj)).symm
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_middle_last F G a s i j hij hi hj
    · exact False.elim ((by decide : ¬ (2 : Fin 3) ≤ 0) hkl)
    · exact False.elim ((by decide : ¬ (2 : Fin 3) ≤ 1) hkl)
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_eq_of_normalized _ _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj F G a s i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj F G a s j)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj_last F G a s i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj_last F G a s j hj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCanonicalSimplex_obj_last F G a s i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCanonicalSimplex_obj_last F G a s j hj)
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_lastHom F G a s i j hij hi hj).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex_lastHom _ _ _ _ i j
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime_one a i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime_one a j hj)).symm
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have hP := Path.le (P.obj 0)
    exact False.elim (hij hP)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
