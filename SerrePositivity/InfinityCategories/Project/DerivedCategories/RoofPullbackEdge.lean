module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.RoofTargetFunctor
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # 二つの指定実辺を持つ pullback の実辺

概要：同じ底の一単体を持つ二つの実辺を、指定端点を保って pullback の実辺にする。
方針：点図式の Yoneda 表示を pullback に持ち上げ、両端点を二射影で照合する。
規約：quasicategory 性や fibration 性は不要。使われ方：任意標的の実屋根評価辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial

/-- 同じ底の実辺の点図式を、pullback の点図式へ持ち上げる。 -/
def roofPullbackEdgeMap {A B C : SSet.{u}} (f : A ⟶ C) (g : B ⟶ C)
    {a b : (pullback f g) _⦋0⦌}
    (u : Truncated.Edge (X := (truncation 2).obj A)
      ((pullback.fst f g).app (Opposite.op ⦋0⦌) a)
      ((pullback.fst f g).app (Opposite.op ⦋0⦌) b))
    (v : Truncated.Edge (X := (truncation 2).obj B)
      ((pullback.snd f g).app (Opposite.op ⦋0⦌) a)
      ((pullback.snd f g).app (Opposite.op ⦋0⦌) b))
    (h : f.app (Opposite.op ⦋1⦌) u.edge = g.app (Opposite.op ⦋1⦌) v.edge) :
    Δ[1] ⟶ pullback f g :=
  pullback.lift (SSet.yonedaEquiv.symm u.edge) (SSet.yonedaEquiv.symm v.edge) (by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h)

/-- 同じ底の二つの指定実辺を、指定両端点の pullback の実辺へ持ち上げる。 -/
def roofPullbackEdge {A B C : SSet.{u}} (f : A ⟶ C) (g : B ⟶ C)
    {a b : (pullback f g) _⦋0⦌}
    (u : Truncated.Edge (X := (truncation 2).obj A)
      ((pullback.fst f g).app (Opposite.op ⦋0⦌) a)
      ((pullback.fst f g).app (Opposite.op ⦋0⦌) b))
    (v : Truncated.Edge (X := (truncation 2).obj B)
      ((pullback.snd f g).app (Opposite.op ⦋0⦌) a)
      ((pullback.snd f g).app (Opposite.op ⦋0⦌) b))
    (h : f.app (Opposite.op ⦋1⦌) u.edge = g.app (Opposite.op ⦋1⦌) v.edge) :
    Truncated.Edge (X := (truncation 2).obj (pullback f g)) a b where
  edge := SSet.yonedaEquiv (roofPullbackEdgeMap f g u v h)
  src_eq := by
    change (pullback f g).δ 1 (SSet.yonedaEquiv (roofPullbackEdgeMap f g u v h)) = a
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    apply SSet.yonedaEquiv.symm.injective
    rw [Equiv.symm_apply_apply]
    apply pullback.hom_ext
    · rw [Category.assoc, roofPullbackEdgeMap, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source]
      exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetPoint (pullback.fst f g) a).symm
    · rw [Category.assoc, roofPullbackEdgeMap, pullback.lift_snd, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source]
      exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetPoint (pullback.snd f g) a).symm
  tgt_eq := by
    change (pullback f g).δ 0 (SSet.yonedaEquiv (roofPullbackEdgeMap f g u v h)) = b
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    apply SSet.yonedaEquiv.symm.injective
    rw [Equiv.symm_apply_apply]
    apply pullback.hom_ext
    · rw [Category.assoc, roofPullbackEdgeMap, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target]
      exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetPoint (pullback.fst f g) b).symm
    · rw [Category.assoc, roofPullbackEdgeMap, pullback.lift_snd, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target]
      exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetPoint (pullback.snd f g) b).symm

section
variable {A B C : SSet.{u}} (f : A ⟶ C) (g : B ⟶ C) {a b : (pullback f g) _⦋0⦌}
variable (u : Truncated.Edge (X := (truncation 2).obj A)
  ((pullback.fst f g).app (Opposite.op ⦋0⦌) a)
  ((pullback.fst f g).app (Opposite.op ⦋0⦌) b))
variable (v : Truncated.Edge (X := (truncation 2).obj B)
  ((pullback.snd f g).app (Opposite.op ⦋0⦌) a)
  ((pullback.snd f g).app (Opposite.op ⦋0⦌) b))
variable (h : f.app (Opposite.op ⦋1⦌) u.edge = g.app (Opposite.op ⦋1⦌) v.edge)

/-- 作った pullback の実辺の第一成分は、元の指定実辺。 -/
lemma roofPullbackEdge_fst :
    (pullback.fst f g).app (Opposite.op ⦋1⦌) (roofPullbackEdge f g u v h).edge = u.edge := by
  change (pullback.fst f g).app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (roofPullbackEdgeMap f g u v h)) = _
  rw [← SSet.yonedaEquiv_comp, roofPullbackEdgeMap, pullback.lift_fst, Equiv.apply_symm_apply]

/-- 作った pullback の実辺の第二成分は、元の指定実辺。 -/
lemma roofPullbackEdge_snd :
    (pullback.snd f g).app (Opposite.op ⦋1⦌) (roofPullbackEdge f g u v h).edge = v.edge := by
  change (pullback.snd f g).app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (roofPullbackEdgeMap f g u v h)) = _
  rw [← SSet.yonedaEquiv_comp, roofPullbackEdgeMap, pullback.lift_snd, Equiv.apply_symm_apply]
end

end SerrePositivity.InfinityCategories.Project.DerivedCategories
