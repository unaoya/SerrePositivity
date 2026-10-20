module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralFinalEdge
public import SerrePositivity.InfinityCategories.Derived.DGOneSimplexComponentExt
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges
public import SerrePositivity.InfinityCategories.DGNerve.DataLowDimensionalPullback
public import SerrePositivity.InfinityCategories.Core.HornPointJoin

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}

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

variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 指定零面の最後二頂点から回収する実一次単体。 -/
def dgGeneralLastHornFinalSimplex : Simplex A D 1 :=
  (σ.app _ (horn.face (Fin.last (n + 2)) 0 (by simp))).pullback
    (dgLastHornFinalPair.{0} n).down.toOrderHom

/-- 指定零面による最後辺の回収は、元の実ホーンの最後辺と厳密に同じ。 -/
lemma dgGeneralLastHornFinalSimplex_eq_actual :
    dgGeneralLastHornFinalSimplex σ = σ.app _ (finalHornEdge n) := by
  have he : (horn (n + 2) (Fin.last (n + 2)) : SSet).map
      (dgLastHornFinalPair.{0} n).down.op (horn.face (Fin.last (n + 2)) 0 (by simp)) =
        finalHornEdge n := by
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
      (HornData.knownData σ).obj (dgLastHornPenultimate n) :=
  HornData.face_obj σ 0 (by simp) ⟨n, by omega⟩

/-- 最後一次単体の終対象は、元の回収対象族の終対象。 -/
lemma dgGeneralLastHornFinalSimplex_target :
    (dgGeneralLastHornFinalSimplex σ).obj 1 =
      (HornData.knownData σ).obj (Fin.last (n + 2)) :=
  HornData.face_obj σ 0 (by simp) (Fin.last (n + 1))

/-- 元の最後辺の回収閉零成分と、同じ実一次単体の成分は異種等号で一致する。 -/
lemma dgGeneralLastHornFinalSimplex_component :
    HEq ((HornData.knownData σ).edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
      (dgLastHornPenultimate_lt_last n))
      ((dgGeneralLastHornFinalSimplex σ).edgeHom 0 1 (by decide)) := by
  let t := σ.app _ (horn.face (Fin.last (n + 2)) 0 (by simp))
  have h₀ := SimplexData.edgeHom_heq_of_pullback_eq (HornData.knownData σ) t.toSimplexData
    (0 : Fin (n + 3)).succAboveOrderEmb.toOrderHom (0 : Fin (n + 3)).succAboveOrderEmb.injective
    (HornData.knownData_pullback_face σ 0 (by simp))
    ⟨n, by change n < n + 2; omega⟩ (Fin.last (n + 1))
    (by change n < n + 1; omega) (dgLastHornPenultimate_lt_last n)
  have h₁ := SimplexData.edgeHom_heq_of_pullback_eq t.toSimplexData
    (dgGeneralLastHornFinalSimplex σ).toSimplexData (dgLastHornFinalPair.{0} n).down.toOrderHom
    (dgLastHornFinalPair_injective.{0} n) rfl 0 1 (by decide) (by change n < n + 1; omega)
  exact h₀.trans h₁

/-- 回収閉零射の実辺は、元の指定ホーンの同じ実最後辺である。 -/
lemma dgGeneralLastHornFinalClosed_edge :
    (dgClosedEdge A D (dgGeneralLastHornFinalClosed σ)).edge = σ.app _ (finalHornEdge n) := by
  have hc : (dgClosedEdge A D (dgGeneralLastHornFinalClosed σ)).edge.edgeHom 0 1 (by decide) =
      (HornData.knownData σ).edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
        (dgLastHornPenultimate_lt_last n) := by
    change (closedHomEquiv A D _ _ ((closedHomEquiv A D _ _).symm
      (dgGeneralLastHornFinalCycle σ))).val = _
    exact congrArg Subtype.val ((closedHomEquiv A D _ _).apply_symm_apply _)
  exact (dgOneSimplex_ext (dgGeneralLastHornFinalSimplex_source σ).symm
    (dgGeneralLastHornFinalSimplex_target σ).symm
      ((heq_of_eq hc).trans (dgGeneralLastHornFinalSimplex_component σ))).trans
        (dgGeneralLastHornFinalSimplex_eq_actual σ)

end SerrePositivity.InfinityCategories
