module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornCochains
public import SerrePositivity.InfinityCategories.Derived.DGBoundaryTopCompletion

/-! # 二未知 cochain の解から実三次最後外ホーンを充填する

概要：回収された Q・A の微分式を満たす二射から、指定全三面を保つ実四面体を構成する。
方針：Q の挿入後の全真部分集合の方程式を使い、最上位 A だけを完成させる。
規約：解の存在を仮定として明示する。使われ方：追加分母後の相対原始元を実整合性へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D)
variable (Q : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 2) (-1))

/-- Q の微分式が解けたとき、A の微分式の右辺は実際に閉じている。 -/
lemma dgLastHornTopResidual_closed_of_Q
    (dQ : differential A Q = dgLastHornMissingResidual σ) :
    differential A (dgLastHornTopResidual σ +
      compose A ((HornData.knownData σ).edgeHom 2 3 (by decide)) Q (by decide)) = 0 := by
  let s := dgLastHornQData σ Q
  have hp : ∀ J ⊂ (Finset.univ : Finset (Fin 4)), s.Equation J := by
    intro J hJ
    exact dgLastHornQData_properEquations σ Q dQ J (Finset.ssubset_iff_subset_ne.mp hJ).2
  have hc := s.differential_rhs_zero_of_proper_equations Finset.univ hp
    0 3 (-2) (by decide) (by decide) (by decide) (by decide)
  exact (congrArg (fun f => differential A f)
    (dgTetrahedronWithQ_rhs_top (HornData.knownData σ) Q)).symm.trans hc

/-- 二つの型付き微分式の解から、元の指定三面を持つ実 dg 四面体を構成する。 -/
def dgLastHornFillerSimplex
    (dQ : differential A Q = dgLastHornMissingResidual σ)
    (a : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3) (-2))
    (da : differential A a = dgLastHornTopResidual σ +
      compose A ((HornData.knownData σ).edgeHom 2 3 (by decide)) Q (by decide)) : Simplex A D 3 :=
  dgCompleteTopSimplex (dgLastHornQData σ Q) (dgLastHornQData_properEquations σ Q dQ)
    0 3 (-2) (by decide) (by decide) (by decide) (by decide) a
      (da.trans (dgTetrahedronWithQ_rhs_top (HornData.knownData σ) Q).symm)

/-- 構成した実四面体は、元のホーンの指定三面を全て厳密に保持する。 -/
lemma dgLastHornFillerSimplex_face
    (dQ : differential A Q = dgLastHornMissingResidual σ)
    (a : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3) (-2))
    (da : differential A a = dgLastHornTopResidual σ +
      compose A ((HornData.knownData σ).edgeHom 2 3 (by decide)) Q (by decide))
    (j : Fin 4) (hj : j ≠ 3) :
    (dgNerve A D).δ j (dgLastHornFillerSimplex σ Q dQ a da) =
      σ.app _ (horn.face 3 j hj) := by
  apply Simplex.ext
  exact (dgCompleteTopSimplex_pullback_face (dgLastHornQData σ Q)
    (dgLastHornQData_properEquations σ Q dQ) 0 3 (-2) (by decide) (by decide)
      (by decide) (by decide) a _ j).trans (dgLastHornQData_face σ Q j hj)

/-- 構成した実四面体の米田表示は、元の指定ホーン全体の延長。 -/
lemma dgLastHornFiller_extension
    (dQ : differential A Q = dgLastHornMissingResidual σ)
    (a : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3) (-2))
    (da : differential A a = dgLastHornTopResidual σ +
      compose A ((HornData.knownData σ).edgeHom 2 3 (by decide)) Q (by decide)) :
    σ = (horn 3 3).ι ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
      (dgLastHornFillerSimplex σ Q dQ a da) := by
  apply SSet.horn.hom_ext
  intro j hj
  rw [← dgLastHornFillerSimplex_face σ Q dQ a da j hj, NatTrans.comp_app]
  rfl

/-- 充填四面体の欠けた三角形成分は、入力した Q そのもの。 -/
lemma dgLastHornFillerSimplex_Q
    (dQ : differential A Q = dgLastHornMissingResidual σ)
    (a : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3) (-2))
    (da : differential A a = dgLastHornTopResidual σ +
      compose A ((HornData.knownData σ).edgeHom 2 3 (by decide)) Q (by decide)) :
    (dgLastHornFillerSimplex σ Q dQ a da).toSimplexData.tripleHom
      0 1 2 (by decide) (by decide) = Q := by
  exact (SimplexData.replaceFixed_hom_of_ne (dgLastHornQData σ Q) Finset.univ 0 3 (-2)
    (by decide) (by decide) (by decide) (by decide) a {0, 1, 2} 0 2 (-1)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (dgTetrahedronWithQ_component (HornData.knownData σ) Q)

/-- 充填四面体の最上位成分は、入力した A そのもの。 -/
lemma dgLastHornFillerSimplex_A
    (dQ : differential A Q = dgLastHornMissingResidual σ)
    (a : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3) (-2))
    (da : differential A a = dgLastHornTopResidual σ +
      compose A ((HornData.knownData σ).edgeHom 2 3 (by decide)) Q (by decide)) :
    (dgLastHornFillerSimplex σ Q dQ a da).hom Finset.univ 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) = a :=
  SimplexData.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories
