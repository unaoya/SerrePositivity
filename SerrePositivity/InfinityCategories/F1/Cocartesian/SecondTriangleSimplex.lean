module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SecondTrianglePureHom
public import SerrePositivity.InfinityCategories.F1.Cocartesian.SecondTriangleLastHom
public import SerrePositivity.InfinityCategories.F1.Cocartesian.SecondTriangleTargetHom

/-!
概要：元の第二三角形の全単体は、同じ零成分と終域輸送の標準合成図式そのもの。
方針：三対象と六つの順方向 Hom の一致を、豊穣関手の外延性で束ねる。
規約：元の全 Hom の全次数を保持し、固定成分の仮定は使わない。
使われ方：元の固定成分比較と標準対角 fiber 比較の厳密な一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の第二三角形の切断単体は、同じ標準合成三角形の切断単体と一致する。 -/
lemma cocartesianSecondTriangleCutSimplex_eq_canonical
    (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌) :
    cocartesianSecondTriangleCutSimplex F G a s =
      cocartesianSecondTriangleCanonicalSimplex F G a s := by
  apply EnrichedFunctor.ext SSet (fun i ↦ cocartesianSecondTriangleCutSimplex_obj F G a s i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  by_cases hij : i ≤ j
  · generalize hi : (stdSimplex.objEquiv a) i = k
    generalize hj : (stdSimplex.objEquiv a) j = l
    have hkl : k ≤ l := by
      rw [← hi, ← hj]
      exact (stdSimplex.objEquiv a).toOrderHom.monotone hij
    fin_cases k <;> fin_cases l
    · apply simplicialHom_eq_of_normalized _ _
        (cocartesianSecondTriangleCutSimplex_obj F G a s i) (cocartesianSecondTriangleCutSimplex_obj F G a s j)
        (cocartesianSecondTriangleCutSimplex_obj_zero F G a s i hi)
        (cocartesianSecondTriangleCutSimplex_obj_zero F G a s j hj)
        (cocartesianSecondTriangleCanonicalSimplex_obj_zero F G a s i hi)
        (cocartesianSecondTriangleCanonicalSimplex_obj_zero F G a s j hj)
      exact (cocartesianSecondTriangleCutSimplex_zeroHom F G a s i j hij hi hj).trans
        (coherentCompositionNestedCutSimplex_zeroHom _ _ _ _ (cocartesianSecondTriangleTime_support a)
          i j (cocartesianSecondTriangleTime_zero a i hi) (cocartesianSecondTriangleTime_zero a j hj)).symm
    · exact cocartesianSecondTriangleCutSimplex_zero_middle F G a s i j hij hi hj
    · exact cocartesianSecondTriangleCutSimplex_zero_last F G a s i j hij hi hj
    · exact False.elim ((by decide : ¬ (1 : Fin 3) ≤ 0) hkl)
    · apply simplicialHom_eq_of_normalized _ _
        (cocartesianSecondTriangleCutSimplex_obj F G a s i) (cocartesianSecondTriangleCutSimplex_obj F G a s j)
        (cocartesianSecondTriangleCutSimplex_obj_middle F G a s i hi)
        (cocartesianSecondTriangleCutSimplex_obj_middle F G a s j hj)
        (cocartesianSecondTriangleCanonicalSimplex_obj_middle F G a s i hi)
        (cocartesianSecondTriangleCanonicalSimplex_obj_middle F G a s j hj)
      exact (cocartesianSecondTriangleCutSimplex_middleHom F G a s i j hij hi hj).trans
        (coherentCompositionNestedCutSimplex_middleHom _ _ _ _ i j
          (cocartesianFirstTriangleTime_zero a i 1 hi) (cocartesianFirstTriangleTime_zero a j 1 hj)
          (cocartesianSecondTriangleTime_one a i 0 hi) (cocartesianSecondTriangleTime_one a j 0 hj)).symm
    · exact cocartesianSecondTriangleCutSimplex_middle_last F G a s i j hij hi hj
    · exact False.elim ((by decide : ¬ (2 : Fin 3) ≤ 0) hkl)
    · exact False.elim ((by decide : ¬ (2 : Fin 3) ≤ 1) hkl)
    · apply simplicialHom_eq_of_normalized _ _
        (cocartesianSecondTriangleCutSimplex_obj F G a s i) (cocartesianSecondTriangleCutSimplex_obj F G a s j)
        (cocartesianSecondTriangleCutSimplex_obj_last F G a s i hi)
        (cocartesianSecondTriangleCutSimplex_obj_last F G a s j hj)
        (cocartesianSecondTriangleCanonicalSimplex_obj_last F G a s i hi)
        (cocartesianSecondTriangleCanonicalSimplex_obj_last F G a s j hj)
      exact (cocartesianSecondTriangleCutSimplex_lastHom F G a s i j hij hi hj).trans
        (coherentCompositionNestedCutSimplex_lastHom _ _ _ _ i j
          (cocartesianFirstTriangleTime_one a i hi) (cocartesianFirstTriangleTime_one a j hj)).symm
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have hP := Path.le (P.obj 0)
    exact False.elim (hij hP)

end SerrePositivity.InfinityCategories
