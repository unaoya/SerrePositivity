module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FirstTriangleZeroHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FirstTriangleMixedHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FirstTriangleOneHom

/-!
概要：元の第一三角形の全単体を、同じ指定合成三角形の制限に厳密に同定する。
方針：対象と三種類の Hom の計算を豊穣関手の外延性で束ねる。
規約：元の source の成分 fiber の全次数のパラメーターを保持する。
使われ方：元の固定成分比較を、指定第一三角形上の fiber へ制限する。

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

/-- 固定成分上の元の第一三角形は、全次数で同じ指定合成三角形の制限。 -/
lemma cocartesianFirstTriangleCutSimplex_eq_canonical
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 1))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌) {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomSourceComponent F G (ULift.up 1)) b) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleCutSimplex F G a s.val.down =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleCanonicalSimplex F G b a := by
  apply EnrichedFunctor.ext SSet
    (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleCutSimplex_obj F G b a s.val.down i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  by_cases hij : i ≤ j
  · generalize hi : (stdSimplex.objEquiv a) i = k
    generalize hj : (stdSimplex.objEquiv a) j = l
    have hkl : k ≤ l := by
      rw [← hi, ← hj]
      exact (stdSimplex.objEquiv a).toOrderHom.monotone hij
    fin_cases k <;> fin_cases l
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleCutSimplex_zeroHom_eq F G b a s.val.down i j hij 0 0 hi hj
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleCutSimplex_zeroHom_eq F G b a s.val.down i j hij 0 1 hi hj
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleCutSimplex_mixedHom_eq F G b a s i j hij 0 hi hj
    · exact False.elim ((by decide : ¬ (1 : Fin 3) ≤ 0) hkl)
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleCutSimplex_zeroHom_eq F G b a s.val.down i j hij 1 1 hi hj
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleCutSimplex_mixedHom_eq F G b a s i j hij 1 hi hj
    · exact False.elim ((by decide : ¬ (2 : Fin 3) ≤ 0) hkl)
    · exact False.elim ((by decide : ¬ (2 : Fin 3) ≤ 1) hkl)
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleCutSimplex_oneHom_eq F G b a s.val.down i j hij hi hj
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have hP := Path.le (P.obj 0)
    exact False.elim (hij hP)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
