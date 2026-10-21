module

public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteConeArrowEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.ArrowFunctorFamilyHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.JoinVertexSummands

/-!
概要：元の全脚の正方形をまとめた矢印全錐を、元の二つの全錐の円柱へ移す。
方針：元の全族を uncurry し、頂点と成分で同じ比較辺を回収して可逆性を示す。
規約：元の全錐・指定比較辺・全脚の可換式を保持する。有限性は不要。
使われ方：元の離散全錐の関手同型による極限性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory
variable {J : Type u} {X : SSet.{u + 1}} [Quasicategory X]
  {p q : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶ X}
  (c : JoinCone p) (d : JoinCone q) (e : SSet.Edge c.vertex d.vertex)
  (f : (j : J) → SSet.Edge
    (p.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk j))))
    (q.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk j)))))
  (h : ∀ j, homMk e.toTruncated ≫
    homMk (F2.nativeConeLeg d (ULift.up (nerveVertex (Discrete.mk j)))) =
    homMk (F2.nativeConeLeg c (ULift.up (nerveVertex (Discrete.mk j)))) ≫
      homMk (f j).toTruncated)

include e f h in
/-- 同じ元の全脚の正方形を、元の二つの全錐の実際の円柱として保持する。 -/
def discreteConeArrowHomotopy : SSet.Homotopy c.val d.val := by
  let D := discreteConeArrowCone c d e f h
  let H := arrowFunctorFamilyHomotopy D.val
  have hz : D.val ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = c.val :=
    congrArg (fun a : JoinCone p => a.val) (discreteConeArrowCone_zero c d e f h)
  have ho : D.val ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = d.val :=
    congrArg (fun a : JoinCone q => a.val) (discreteConeArrowCone_one c d e f h)
  exact ⟨H.h, H.h₀.trans hz, H.h₁.trans ho, H.rel⟩

/-- 元の頂点比較と全成分比較が可逆なら、同じ元の全錐円柱は全頂点で可逆。 -/
lemma discreteConeArrowHomotopy_isInvertible
    (he : IsInvertibleEdge e.toTruncated) (hf : ∀ j, IsInvertibleEdge (f j).toTruncated)
    (x : (join (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)))) _⦋0⦌) :
    IsInvertibleEdge
      (simplicialHomotopyVertexEdge (discreteConeArrowHomotopy c d e f h) x).toTruncated := by
  let K := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J))
  let D := discreteConeArrowCone c d e f h
  obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := joinVertexSummands x
  · have ha : a = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})) := by
      apply stdSimplex.obj₀Equiv.injective
      apply Fin.ext
      have ha₀ := (stdSimplex.obj₀Equiv a).isLt
      have hp₀ := (stdSimplex.obj₀Equiv (SSet.yonedaEquiv
        (𝟙 (Δ[0] : SSet.{u + 1})))).isLt
      omega
    have hv : D.val.app (Opposite.op ⦋0⦌) ((joinInl Δ[0] K).app _ a) =
        functorVertex (SSet.yonedaEquiv.symm e.edge) := by
      subst a
      exact discreteConeArrowCone_vertex c d e f h
    apply (isInvertibleEdge_congr
      (e := (simplicialHomotopyVertexEdge (discreteConeArrowHomotopy c d e f h)
        ((joinInl Δ[0] K).app _ a)).toTruncated) (f := e.toTruncated) ?_).mpr he
    exact arrowFunctorFamilyHomotopy_vertex D.val _ e hv
  · let j := (b.down.obj 0).as
    have hv : D.val.app (Opposite.op ⦋0⦌) ((joinInr Δ[0] K).app _ b) =
        functorVertex (SSet.yonedaEquiv.symm (f j).edge) := by
      have H := congrArg (fun a => a.app (Opposite.op ⦋0⦌) b) D.property
      exact H.trans (pinchedConstant_zero (functorVertex (SSet.yonedaEquiv.symm (f j).edge)))
    apply (isInvertibleEdge_congr
      (e := (simplicialHomotopyVertexEdge (discreteConeArrowHomotopy c d e f h)
        ((joinInr Δ[0] K).app _ b)).toTruncated) (f := (f j).toTruncated) ?_).mpr (hf j)
    exact arrowFunctorFamilyHomotopy_vertex D.val _ (f j) hv

end SerrePositivity.InfinityCategories.HomotopyLimits
