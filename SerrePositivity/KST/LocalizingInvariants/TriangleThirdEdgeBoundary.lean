module

public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanBoundary

/-!
概要：三角形族の第三辺の両端は、初頂点 horn への制限だけで決まる。
方針：二つの頂点評価を horn の二脚の終点評価へ戻す。
規約：等式は全パラメーター上で厳密。三角形の合成辺自体の等式は要求しない。
使われ方：任意の実三角補完の第三辺を固定端点の写像空間に入れる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {A Q : SSet.{u}}

lemma triangleThirdEdge_source (f : A ⟶ (ihom (Δ[2] : SSet.{u})).obj Q) :
    (f ≫ (pre (stdSimplex.δ (0 : Fin 3))).app Q) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (f ≫ (pre (horn 2 0).ι).app Q) ≫ (pre horn₂₀.ι₀₁).app Q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

lemma triangleThirdEdge_target (f : A ⟶ (ihom (Δ[2] : SSet.{u})).obj Q) :
    (f ≫ (pre (stdSimplex.δ (0 : Fin 3))).app Q) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (f ≫ (pre (horn 2 0).ι).app Q) ≫ (pre horn₂₀.ι₀₂).app Q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

lemma triangleThirdEdge_boundary_eq {f g : A ⟶ (ihom (Δ[2] : SSet.{u})).obj Q}
    (h : f ≫ (pre (horn 2 0).ι).app Q = g ≫ (pre (horn 2 0).ι).app Q) :
    (f ≫ (pre (stdSimplex.δ (0 : Fin 3))).app Q) ≫ (pre (boundary 1).ι).app Q =
      (g ≫ (pre (stdSimplex.δ (0 : Fin 3))).app Q) ≫ (pre (boundary 1).ι).app Q := by
  rw [intervalFunctor_restrict_boundary, intervalFunctor_restrict_boundary,
    triangleThirdEdge_source, triangleThirdEdge_source,
    triangleThirdEdge_target, triangleThirdEdge_target, h]

end SerrePositivity.KST.LocalizingInvariants
