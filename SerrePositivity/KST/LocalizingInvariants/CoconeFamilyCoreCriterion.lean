module

public import SerrePositivity.KST.LocalizingInvariants.FixedSpanApexDenominators
public import SerrePositivity.KST.LocalizingInvariants.SimplexAttachmentEquivalences
public import SerrePositivity.InfinityCategories.F1B.Joins.JoinPrismFixed

/-!
概要：余錐全族の前段と頂点の辺反転から、その同じ全族の辺反転を証明する。
方針：指定されたパラメータ辺を全図式頂点で検査し、join の二因子で尽くす。
規約：パラメータやその区間に Kan 性を仮定せず、元の実全族を変更しない。
使われ方：実分母円柱の商像を元の全図式 core へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma functorFamily_invertsEdges_of_evaluations {P L X : SSet.{u}} [Quasicategory X]
    (F : P ⟶ (ihom L).obj X) (W : Set (P _⦋1⦌))
    (hF : ∀ l : L _⦋0⦌, InvertsEdges (F ≫ evaluateFunctorAt l) W) :
    InvertsEdges F W := by
  intro s hs
  let a := edgeOfSimplex (F.app (Opposite.op ⦋1⦌) s)
  let f := (functorVertexEquiv L X).symm ((ihom L).obj X |>.δ 1 (F.app (Opposite.op ⦋1⦌) s))
  let g := (functorVertexEquiv L X).symm ((ihom L).obj X |>.δ 0 (F.app (Opposite.op ⦋1⦌) s))
  let e : Truncated.Edge (X := (truncation 2).obj ((ihom L).obj X))
      (functorVertex f) (functorVertex g) :=
    ((SSet.Edge.ofTruncated a).ofEq
      ((functorVertexEquiv L X).apply_symm_apply _).symm
      ((functorVertexEquiv L X).apply_symm_apply _).symm).toTruncated
  apply (isInvertibleEdge_congr (e := e)
    (f := (edgeOfSimplex s).map ((truncation 2).map F)) rfl).mp
  apply (isInvertibleEdge_iff_evaluateFunctorAt e).mpr
  intro l
  exact (isInvertibleEdge_congr (e := e.map ((truncation 2).map (evaluateFunctorAt l)))
    (f := (edgeOfSimplex s).map ((truncation 2).map (F ≫ evaluateFunctorAt l))) rfl).mpr
      (hF l hs)

/-- 前段の全辺と固定頂点が与える、同じ全余錐族の全パラメータ辺の反転。 -/
lemma coconeFamily_invertsAllEdges_of_prefix_apex {P L X : SSet.{u}} [Quasicategory X]
    (F : P ⟶ (ihom (join L (Δ[0] : SSet.{u}))).obj X) (z : X _⦋0⦌)
    (hp : InvertsEdges (F ≫ (pre (joinInl L Δ[0])).app X) Set.univ)
    (hz : F ≫ evaluateFunctorAt ((joinInr L (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z) :
    InvertsEdges F Set.univ := by
  apply functorFamily_invertsEdges_of_evaluations
  intro v
  rcases F1B.join_vertex_cases L Δ[0] v with ⟨l, rfl⟩ | ⟨b, rfl⟩
  · rw [← stable_pre_evaluateFunctorAt (X := X) (joinInl L Δ[0]) l, ← Category.assoc]
    intro s hs
    exact (hp hs).map (evaluateFunctorAt l)
  · have hb : b = stdSimplex.obj₀Equiv.symm (0 : Fin 1) := by
      apply stdSimplex.obj₀Equiv.injective
      rw [Equiv.apply_symm_apply]
      exact Fin.eq_zero _
    subst b
    rw [hz]
    exact invertsEdges_const _ _ _ Set.univ

end SerrePositivity.KST.LocalizingInvariants
