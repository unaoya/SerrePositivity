module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornCochains
public import SerrePositivity.InfinityCategories.Derived.DGFourSimplexQReplacement
public import SerrePositivity.InfinityCategories.Derived.DGBoundaryTopCompletion

/-! # 二未知 cochain の解から実四次最後外ホーンを充填する

概要：回収された Q・A の微分式を満たす二射から、指定全四面を保つ実四単体を構成する。
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
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 実四次最後ホーンの最上位微分式の、Q を含まない既知部分。 -/
def dgFourLastHornTopResidual := dgFourSimplexTopResidual (HornData.knownData σ)

variable (Q : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3) (-2))

/-- Q の微分式が解けたとき、A の微分式の右辺は実際に閉じている。 -/
lemma dgFourLastHornTopResidual_closed_of_Q
    (dQ : differential A Q = dgFourLastHornMissingResidual σ) :
    differential A (dgFourLastHornTopResidual σ +
      compose A ((HornData.knownData σ).edgeHom 3 4 (by decide)) Q (by decide)) = 0 := by
  let s := dgFourLastHornQData σ Q
  have hp : ∀ J ⊂ (Finset.univ : Finset (Fin 5)), s.Equation J := by
    intro J hJ
    exact dgFourLastHornQData_properEquations σ Q dQ J (Finset.ssubset_iff_subset_ne.mp hJ).2
  have hc := s.differential_rhs_zero_of_proper_equations Finset.univ hp
    0 4 (-3) (by decide) (by decide) (by decide) (by decide)
  exact (congrArg (fun f => differential A f)
    (dgFourSimplexWithQ_rhs_top (HornData.knownData σ) Q)).symm.trans hc

/-- 二つの型付き微分式の解から、元の指定四面を持つ実 dg 四単体を構成する。 -/
def dgFourLastHornFillerSimplex
    (dQ : differential A Q = dgFourLastHornMissingResidual σ)
    (a : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 4) (-3))
    (da : differential A a = dgFourLastHornTopResidual σ +
      compose A ((HornData.knownData σ).edgeHom 3 4 (by decide)) Q (by decide)) : Simplex A D 4 :=
  dgCompleteTopSimplex (dgFourLastHornQData σ Q) (dgFourLastHornQData_properEquations σ Q dQ)
    0 4 (-3) (by decide) (by decide) (by decide) (by decide) a
      (da.trans (dgFourSimplexWithQ_rhs_top (HornData.knownData σ) Q).symm)

/-- 構成した実四単体は、元のホーンの指定四面を全て厳密に保持する。 -/
lemma dgFourLastHornFillerSimplex_face
    (dQ : differential A Q = dgFourLastHornMissingResidual σ)
    (a : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 4) (-3))
    (da : differential A a = dgFourLastHornTopResidual σ +
      compose A ((HornData.knownData σ).edgeHom 3 4 (by decide)) Q (by decide))
    (j : Fin 5) (hj : j ≠ 4) :
    (dgNerve A D).δ j (dgFourLastHornFillerSimplex σ Q dQ a da) =
      σ.app _ (horn.face 4 j hj) := by
  apply Simplex.ext
  exact (dgCompleteTopSimplex_pullback_face (dgFourLastHornQData σ Q)
    (dgFourLastHornQData_properEquations σ Q dQ) 0 4 (-3) (by decide) (by decide)
      (by decide) (by decide) a _ j).trans (dgFourLastHornQData_face σ Q j hj)

/-- 構成した実四単体の米田表示は、元の指定ホーン全体の延長。 -/
lemma dgFourLastHornFiller_extension
    (dQ : differential A Q = dgFourLastHornMissingResidual σ)
    (a : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 4) (-3))
    (da : differential A a = dgFourLastHornTopResidual σ +
      compose A ((HornData.knownData σ).edgeHom 3 4 (by decide)) Q (by decide)) :
    σ = (horn 4 4).ι ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
      (dgFourLastHornFillerSimplex σ Q dQ a da) := by
  apply SSet.horn.hom_ext
  intro j hj
  rw [← dgFourLastHornFillerSimplex_face σ Q dQ a da j hj, NatTrans.comp_app]
  rfl

/-- 充填四単体の欠けた三次面の最上位成分は、入力した Q そのもの。 -/
lemma dgFourLastHornFillerSimplex_Q
    (dQ : differential A Q = dgFourLastHornMissingResidual σ)
    (a : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 4) (-3))
    (da : differential A a = dgFourLastHornTopResidual σ +
      compose A ((HornData.knownData σ).edgeHom 3 4 (by decide)) Q (by decide)) :
    (dgFourLastHornFillerSimplex σ Q dQ a da).toSimplexData.hom
      {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide) = Q := by
  exact (SimplexData.replaceFixed_hom_of_ne (dgFourLastHornQData σ Q) Finset.univ 0 4 (-3)
    (by decide) (by decide) (by decide) (by decide) a {0, 1, 2, 3} 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (dgFourSimplexWithQ_component (HornData.knownData σ) Q)

/-- 充填四単体の最上位成分は、入力した A そのもの。 -/
lemma dgFourLastHornFillerSimplex_A
    (dQ : differential A Q = dgFourLastHornMissingResidual σ)
    (a : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 4) (-3))
    (da : differential A a = dgFourLastHornTopResidual σ +
      compose A ((HornData.knownData σ).edgeHom 3 4 (by decide)) Q (by decide)) :
    (dgFourLastHornFillerSimplex σ Q dQ a da).hom Finset.univ 0 4 (-3)
      (by decide) (by decide) (by decide) (by decide) = a :=
  SimplexData.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories
