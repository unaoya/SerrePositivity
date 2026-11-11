module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornLastTerm
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralComponents
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LeftCutReplacement

/-! # 一般最後外ホーンの最上位 rhs の二未知分解

概要：Q 挿入による最上位 rhs の変化は、同じ最後辺による Q の後合成そのもの。
方針：左切断置換で変化を一寄与へ制限し、削除・右切断の保存と欠面の零を使う。
規約：元の実 rhs と同じ符号。使われ方：一般残差 cone の K と R の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
variable (Q : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)) (-(n : ℤ)))

/-- 元の既知データの最上位 rhs は、Q を含まない同じ既知残差 K。 -/
def dgGeneralLastHornTopResidual := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTopRhs (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ)

/-- Q 挿入後の最上位 rhs を、元の対象族の斉次 Hom として読む。 -/
def dgGeneralLastHornRhsWithQ :
    GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2))) (-(n : ℤ) - 1 + 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTopRhs (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData σ Q)

/-- Q 挿入後の最後の一寄与を、元の対象族の斉次 Hom として読む。 -/
def dgGeneralLastHornLastTermWithQ :
    GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2))) (-(n : ℤ) - 1 + 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastTerm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData σ Q)

/-- 最後辺による Q の後合成を、最上位微分の同じ次数で読む。 -/
def dgGeneralLastHornPostcomposeQ :
    GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2))) (-(n : ℤ) - 1 + 1) :=
  compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) Q (by omega)

/-- Q 挿入は最後の実辺成分を変えない。 -/
lemma dgGeneralLastHornQData_lastEdge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData σ Q).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n)
    0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_two n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_min n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_max n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_degree n) Q _ _ _ _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastCut_right_ne_missing n)

/-- Q 挿入は最後内部頂点の削除成分を変えない。 -/
lemma dgGeneralLastHornQData_lastErased :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastErased (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData σ Q) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastErased (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n)
    0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_two n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_min n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_max n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_degree n) Q _ _ _ _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastCut_erase_ne_missing n)

/-- Q 挿入後の最後の切断合成は、元の最後辺による同じ Q の後合成。 -/
lemma dgGeneralLastHornQData_lastComposite :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastComposite (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData σ Q) =
      dgGeneralLastHornPostcomposeQ σ Q := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastComposite dgGeneralLastHornPostcomposeQ
  rw [dgGeneralLastHornQData_lastEdge, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData_component]

/-- 元の既知データの最後の切断合成は、未知欠面成分が零なので零。 -/
lemma dgGeneralLastHornKnown_lastComposite_zero :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastComposite (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastComposite
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingHom_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero]

/-- 最上位 rhs の変化は、最後内部頂点の一寄与の変化だけ。 -/
lemma dgGeneralLastHornQData_rhs_difference :
    dgGeneralLastHornRhsWithQ σ Q - dgGeneralLastHornTopResidual σ =
      dgGeneralLastHornLastTermWithQ σ Q - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastTerm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).rhs_replace_leftCut Finset.univ 0 (Fin.last (n + 2))
    (-(n : ℤ) - 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_two n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_min n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_max n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_degree n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Finset.mem_univ _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastCut_left] at h
  exact h ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).fixedHomFamily (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n)
    0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_two n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_min n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_max n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_degree n) Q)

/-- 一般最上位 rhs は、既知 K と最後辺による同じ Q の後合成の和。 -/
lemma dgGeneralLastHornQData_rhs_top :
    dgGeneralLastHornRhsWithQ σ Q =
      dgGeneralLastHornTopResidual σ + dgGeneralLastHornPostcomposeQ σ Q := by
  have hd := dgGeneralLastHornQData_rhs_difference σ Q
  unfold dgGeneralLastHornLastTermWithQ at hd
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastTerm_formula, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastTerm_formula,
    dgGeneralLastHornQData_lastErased, dgGeneralLastHornQData_lastComposite,
    dgGeneralLastHornKnown_lastComposite_zero] at hd
  let e : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2))) (-(n : ℤ) - 1 + 1) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastErased (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ)
  have hc : -e + dgGeneralLastHornPostcomposeQ σ Q - (-e + 0) =
      dgGeneralLastHornPostcomposeQ σ Q := by abel
  have h : dgGeneralLastHornRhsWithQ σ Q - dgGeneralLastHornTopResidual σ =
      dgGeneralLastHornPostcomposeQ σ Q := hd.trans hc
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
