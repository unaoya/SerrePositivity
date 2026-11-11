module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralFinalEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOneSimplexComponentExt
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataLowDimensionalPullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.HornPointJoin

/-! # 一般最後ホーンの実最後辺と回収閉辺の一致

概要：元のホーンの実最後辺は、回収した最後閉零射から作る実辺そのものである。
方針：指定零面の最後二頂点への制限を、自然性と型付き辺成分で照合する。
規約：対象・斉次成分・実単体を厳密に比較。使われ方：実 over 境界の最後辺の分母性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}

/-- 指定零面の最後二頂点を選ぶ、同じ標準辺。 -/
def dgLastHornFinalPair (n : ℕ) : Δ[n + 1] _⦋1⦌ :=
  SSet.stdSimplex.edge (n + 1) ⟨n, by change n < n + 2; omega⟩ (Fin.last (n + 1)) (Fin.le_last _)

/-- 最後二頂点への添字写像は単射。 -/
lemma dgLastHornFinalPair_injective (n : ℕ) :
    Function.Injective (dgLastHornFinalPair.{u} n).down.toOrderHom := by
  intro a b h
  fin_cases a <;> fin_cases b
  · rfl
  · have hv := congrArg Fin.val h
    change n = n + 1 at hv
    omega
  · have hv := congrArg Fin.val h
    change n + 1 = n at hv
    omega
  · rfl

variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 指定零面の最後二頂点から回収する実一次単体。 -/
def dgGeneralLastHornFinalSimplex : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 :=
  (σ.app _ (horn.face (Fin.last (n + 2)) 0 (by simp))).pullback
    (dgLastHornFinalPair.{0} n).down.toOrderHom

/-- 指定零面による最後辺の回収は、元の実ホーンの最後辺と厳密に同じ。 -/
lemma dgGeneralLastHornFinalSimplex_eq_actual :
    dgGeneralLastHornFinalSimplex σ = σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n) := by
  have he : (horn (n + 2) (Fin.last (n + 2)) : SSet).map
      (dgLastHornFinalPair.{0} n).down.op (horn.face (Fin.last (n + 2)) 0 (by simp)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n := by
    apply Subtype.ext
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  have hn := ConcreteCategory.congr_hom (σ.naturality (dgLastHornFinalPair.{0} n).down.op)
    (horn.face (Fin.last (n + 2)) 0 (by simp))
  change σ.app _ ((horn (n + 2) (Fin.last (n + 2)) : SSet).map
    (dgLastHornFinalPair.{0} n).down.op (horn.face (Fin.last (n + 2)) 0 (by simp))) =
      dgGeneralLastHornFinalSimplex σ at hn
  rw [he] at hn
  exact hn.symm

/-- 最後一次単体の始対象は、元の回収対象族の最後直前の対象。 -/
lemma dgGeneralLastHornFinalSimplex_source :
    (dgGeneralLastHornFinalSimplex σ).obj 0 =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.face_obj σ 0 (by simp) ⟨n, by omega⟩

/-- 最後一次単体の終対象は、元の回収対象族の終対象。 -/
lemma dgGeneralLastHornFinalSimplex_target :
    (dgGeneralLastHornFinalSimplex σ).obj 1 =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.face_obj σ 0 (by simp) (Fin.last (n + 1))

/-- 元の最後辺の回収閉零成分と、同じ実一次単体の成分は異種等号で一致する。 -/
lemma dgGeneralLastHornFinalSimplex_component :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n))
      ((dgGeneralLastHornFinalSimplex σ).edgeHom 0 1 (by decide)) := by
  let t := σ.app _ (horn.face (Fin.last (n + 2)) 0 (by simp))
  have h₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) t.toSimplexData
    (0 : Fin (n + 3)).succAboveOrderEmb.toOrderHom (0 : Fin (n + 3)).succAboveOrderEmb.injective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face σ 0 (by simp))
    ⟨n, by change n < n + 2; omega⟩ (Fin.last (n + 1))
    (by change n < n + 1; omega) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq t.toSimplexData
    (dgGeneralLastHornFinalSimplex σ).toSimplexData (dgLastHornFinalPair.{0} n).down.toOrderHom
    (dgLastHornFinalPair_injective.{0} n) rfl 0 1 (by decide) (by change n < n + 1; omega)
  exact h₀.trans h₁

/-- 回収閉零射の実辺は、元の指定ホーンの同じ実最後辺である。 -/
lemma dgGeneralLastHornFinalClosed_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)).edge = σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n) := by
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)).edge.edgeHom 0 1 (by decide) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n) := by
    change (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalCycle σ))).val = _
    exact congrArg Subtype.val ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).apply_symm_apply _)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOneSimplex_ext (dgGeneralLastHornFinalSimplex_source σ).symm
    (dgGeneralLastHornFinalSimplex_target σ).symm
      ((heq_of_eq hc).trans (dgGeneralLastHornFinalSimplex_component σ))).trans
        (dgGeneralLastHornFinalSimplex_eq_actual σ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
