module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationUnderComparison
public import SerrePositivity.InfinityCategories.Core.UniverseLimits
/-!
概要：指定下側変換を含む補間全族と、その元の旧部分への実余錐。
方針：元の始点評価の等式で pullback へ束ね、全族の制限を二射影で回収する。
規約：元の全余錐と指定変換を保持する。
使われ方：始点評価の under comma の試験族への相対余錐の輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A L : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)
local notation "E" => diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
variable (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
  leftKanShape (indYoneda κ C)
    (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))))
  (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder z)
  (ht : q ≫ diagramCommaEvaluation κ D
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = t ≫ sliceUnderProjection z)
  (P : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⟶ sliceUnder z)
  (hP : (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ P = t)
  (hVP : V.sourceCone ≫ diagramConePointRestriction κ D
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = P ≫ sliceUnderProjection z)
/-- 概要：同じ下側変換の全余錐を持つ元の補間全族を実 under comma へ束ねる。
方針：始点評価を厳密に回収する。規約：元の全射を保持。使われ方：相対余錐。 -/
def indArrowInterpolationUnderFamily :=
  relativeCommaFamily E z P (indArrowInterpolationCommaFamily V)
    ((indArrowInterpolationCommaFamily_source V).trans hVP)
include hP in
/-- 概要：元の旧部分への制限は、同じ指定下側変換を持つ旧族そのもの。
方針：pullback の二射影で検査する。規約：厳密な等式。使われ方：余錐の境界の回収。 -/
lemma indArrowInterpolationUnderFamily_old :
    (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫
      indArrowInterpolationUnderFamily V z P hVP =
    relativeCommaFamily E z t (indArrowInterpolationOldFamily V)
      ((indArrowInterpolationOldFamily_source V).trans ht) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, indArrowInterpolationUnderFamily,
      relativeCommaFamily, pullback.lift_fst]
    exact hP
  · simp only [Category.assoc, indArrowInterpolationUnderFamily,
      relativeCommaFamily, pullback.lift_snd]
    rfl
/-- 概要：同じ全族自体が、指定変換を含む旧族への実余錐を与える。
方針：join の宇宙同型で形状を戻す。規約：元の全族を保持。使われ方：元の q への輸送。 -/
def indArrowInterpolationUnderOldFamilyCocone : JoinCocone
    (relativeCommaFamily E z t (indArrowInterpolationOldFamily V)
      ((indArrowInterpolationOldFamily_source V).trans ht)) :=
  ⟨(uliftCoconeShapeIso.{u, u + 1} A 0).inv ≫
    indArrowInterpolationUnderFamily V z P hVP, by
      rw [← Category.assoc, uliftCoconeShapeIso_inv_inl]
      exact indArrowInterpolationUnderFamily_old V z t ht P hP hVP⟩
end SerrePositivity.InfinityCategories.F2.Ind
