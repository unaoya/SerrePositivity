module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTetrahedronQReplacement
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ProperEquationBianchi

/-! # 実三次最後外ホーンの回収残差と未知 Q

概要：指定ホーンから既知全成分を回収し、欠けた三角形の閉じた右辺と Q の挿入を与える。
方針：元のホーンの既知方程式、Bianchi、固定一射の置換を接続する。
規約：指定三面を厳密に保つ。使われ方：二未知 cochain による実ホーン充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 実ホーンの欠けた三角形の微分式の回収された右辺。 -/
def dgLastHornMissingResidual := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedronMissingResidual (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ)

/-- 実ホーンの最上位微分式の回収された既知部分。 -/
def dgLastHornTopResidual := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedronTopResidual (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ)

/-- 欠けた三角形の右辺は、実ホーンの既知の真部分集合の方程式から閉じている。 -/
lemma dgLastHornMissingResidual_closed : _root_.SerrePositivity.DifferentialGraded.differential A (dgLastHornMissingResidual σ) = 0 := by
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ
  have hp : ∀ J ⊂ ({0, 1, 2} : Finset (Fin 4)), s.Equation J := by
    intro J hJ
    have hf : J ≠ Finset.univ := by
      intro he
      have h₃ : (3 : Fin 4) ∈ J := he.symm ▸ Finset.mem_univ 3
      exact (by decide : (3 : Fin 4) ∉ ({0, 1, 2} : Finset (Fin 4))) (hJ.1 h₃)
    have hm : J ≠ Finset.univ.erase (3 : Fin 4) := by
      intro he
      exact (Finset.ssubset_iff_subset_ne.mp hJ).2 (he.trans (by decide))
    intro a b k hI ha hb hk
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_equation σ J a b k hI ha hb hk hf hm
  have hc := s.differential_rhs_zero_of_proper_equations {0, 1, 2} hp
    0 2 (-1) (by decide) (by decide) (by decide) (by decide)
  exact (congrArg (fun f => differential A f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_rhs_missing s)).symm.trans hc

variable (Q : _root_.SerrePositivity.DifferentialGraded.GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2) (-1))

/-- 実ホーンの未知三角形だけを Q で置き換えたデータ。 -/
def dgLastHornQData : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedronWithQ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) Q

/-- Q の挿入は、元のホーンの指定三面を全て厳密に保持する。 -/
lemma dgLastHornQData_face (j : Fin 4) (hj : j ≠ 3) :
    (dgLastHornQData σ Q).pullback j.succAboveOrderEmb.toOrderHom =
      (σ.app _ (horn.face 3 j hj)).toSimplexData := by
  have hm : j ∈ ({0, 1, 2} : Finset (Fin 4)) := by
    rw [show ({0, 1, 2} : Finset (Fin 4)) = Finset.univ.erase 3 from by decide]
    exact Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
  unfold dgLastHornQData _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedronWithQ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_pullback_of_omits _ _ _ _ j hm (Fin.succAbove_ne j)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face σ j hj

/-- Q の微分式が成り立てば、欠けた面の全方程式が成り立つ。 -/
lemma dgLastHornQData_missingEquation
    (dQ : _root_.SerrePositivity.DifferentialGraded.differential A Q = dgLastHornMissingResidual σ) :
    (dgLastHornQData σ Q).Equation {0, 1, 2} := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed _ {0, 1, 2} 0 2 (-1)
    (by decide) (by decide) (by decide) (by decide)
  have hl : (dgLastHornQData σ Q).hom {0, 1, 2} 0 2 (-1)
      (by decide) (by decide) (by decide) (by decide) = Q :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedronWithQ_component (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) Q
  have hr : (dgLastHornQData σ Q).rhs {0, 1, 2} 0 2 (-1)
      (by decide) (by decide) (by decide) (by decide) = dgLastHornMissingResidual σ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_rhs_self (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) {0, 1, 2} 0 2 (-1)
      (by decide) (by decide) (by decide) (by decide) Q).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_rhs_missing (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ))
  exact (congrArg (fun f => _root_.SerrePositivity.DifferentialGraded.differential A f) hl).trans (dQ.trans hr.symm)

/-- Q の微分式が成り立てば、最上位以外の全方程式が成り立つ。 -/
lemma dgLastHornQData_properEquations
    (dQ : _root_.SerrePositivity.DifferentialGraded.differential A Q = dgLastHornMissingResidual σ)
    (I : Finset (Fin 4)) (hf : I ≠ Finset.univ) : (dgLastHornQData σ Q).Equation I := by
  by_cases hm : I = {0, 1, 2}
  · subst I
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornQData_missingEquation σ Q dQ
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.equation_of_faces σ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornQData_face σ Q) I hf
    simpa only [show (Finset.univ : Finset (Fin 4)).erase 3 = {0, 1, 2} from by decide] using hm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
