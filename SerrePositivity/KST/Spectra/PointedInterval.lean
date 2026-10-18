module

public import SerrePositivity.KST.Spectra.PointedEnrichment
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
概要：始点を基点とする単体的区間と終点の包含。
方針：自由な基点を持つ零次球面から区間への端点射を構成する。
規約：始点は零、終点は一。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。loop の次数移動の path fiber 列。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：始点を基点とする単体的区間。
方針：Δ[1] の頂点零に基点を付ける。
規約：区間自身に Kan 性は要求しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。path space の源。 -/
def pointedInterval : PointedSimplicialSet.{u} :=
  PointedSimplicialSet.ofVertex (Δ[1] : SSet.{u}) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

/-- 概要：零次球面の非基点を区間の終点へ送る。
方針：基点を始点に固定し、自由基点の普遍性を使う。
規約：定義域は点つき smash の単位。
使われ方：Kerodon §3.2.5、Goerss–Jardine I §7。path の終点評価。 -/
def intervalEndpoint : 𝟙_ PointedSimplicialSet.{u} ⟶ pointedInterval.{u} :=
  (PointedSimplicialSet.unitVertexEquiv pointedInterval).symm
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

/-- 概要：終点包含の基礎射は二つの端点を指定する余積からの射。
方針：自由基点と頂点の同値の定義を読む。
規約：余積の第一成分が終点、第二成分が基点である始点。
使われ方：Goerss–Jardine I §7。終点包含の単射性。 -/
theorem intervalEndpoint_right : intervalEndpoint.{u}.right =
    coprod.desc (SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := rfl

/-- 概要：単体集合の二項余積の単体は二つの成分のいずれかに属する。
方針：評価関手が余積を保つことと型の余極限の全射性を使う。
規約：任意の単体次数 m。
使われ方：Kerodon §3.1.3。端点包含の単射性の成分ごとの検査。 -/
theorem coprod_simplex_cases (A B : SSet.{u}) (m : SimplexCategoryᵒᵖ) (s : (A ⨿ B).obj m) :
    (∃ a, (coprod.inl : A ⟶ A ⨿ B).app m a = s) ∨
      (∃ b, (coprod.inr : B ⟶ A ⨿ B).app m b = s) := by
  let F := (evaluation SimplexCategoryᵒᵖ (Type u)).obj m
  have hc := isColimitOfHasBinaryCoproductOfPreservesColimit F A B
  have hcompl := ((Types.binaryCofan_isColimit_iff _).mp ⟨hc⟩).2.2
  have hs : s ∈ Set.range (F.map (coprod.inl : A ⟶ A ⨿ B)) ∪
      Set.range (F.map (coprod.inr : B ⟶ A ⨿ B)) := by
    have he : Set.range (F.map (coprod.inl : A ⟶ A ⨿ B)) ∪
        Set.range (F.map (coprod.inr : B ⟶ A ⨿ B)) = Set.univ := hcompl.sup_eq_top
    rw [he]
    trivial
  exact hs

/-- 概要：区間の終点射は余積の第一成分を終点へ送る。
方針：余積からの射の第一成分を計算する。
規約：第一成分は非基点側。
使われ方：Goerss–Jardine I §7。終点包含の単射性。 -/
@[reassoc (attr := simp)]
theorem intervalEndpoint_inl :
    (coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫ intervalEndpoint.right =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  rw [intervalEndpoint_right, coprod.inl_desc]

/-- 概要：区間の終点射は余積の第二成分を始点へ送る。
方針：余積からの射の第二成分を計算する。
規約：第二成分は基点側。
使われ方：Goerss–Jardine I §7。終点包含の単射性。 -/
@[reassoc (attr := simp)]
theorem intervalEndpoint_inr :
    (coprod.inr : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫ intervalEndpoint.right =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [intervalEndpoint_right, coprod.inr_desc]

/-- 概要：終点射の第一成分の像の頂点は一。
方針：定数単体の頂点を計算する。
規約：任意の単体次数 m の先頭頂点で評価する。
使われ方：Kerodon §3.1.3。両端点の像が交わらないことの検査。 -/
theorem intervalEndpoint_inl_value (m : SimplexCategoryᵒᵖ) (a : (𝟙_ SSet.{u}).obj m) :
    (stdSimplex.objEquiv (intervalEndpoint.right.app m
      ((coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})).app m a))).toOrderHom 0 = 1 := by
  change (stdSimplex.objEquiv (((coprod.inl : 𝟙_ SSet.{u} ⟶
    (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫ intervalEndpoint.{u}.right).app m a)).toOrderHom 0 = 1
  rw [intervalEndpoint_inl]
  rfl

/-- 概要：終点射の第二成分の像の頂点は零。
方針：定数単体の頂点を計算する。
規約：任意の単体次数 m の先頭頂点で評価する。
使われ方：Kerodon §3.1.3。両端点の像が交わらないことの検査。 -/
theorem intervalEndpoint_inr_value (m : SimplexCategoryᵒᵖ) (a : (𝟙_ SSet.{u}).obj m) :
    (stdSimplex.objEquiv (intervalEndpoint.right.app m
      ((coprod.inr : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})).app m a))).toOrderHom 0 = 0 := by
  change (stdSimplex.objEquiv (((coprod.inr : 𝟙_ SSet.{u} ⟶
    (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫ intervalEndpoint.{u}.right).app m a)).toOrderHom 0 = 0
  rw [intervalEndpoint_inr]
  rfl

/-- 概要：基点と終点を区間へ送る点つき射は単射。
方針：各単体を余積の成分に分け、二端点の像の非交差性を使う。
規約：基礎単体集合の単射性。
使われ方：Kerodon §3.1.3、Goerss–Jardine I §7。path の終点評価の fibration 性。 -/
instance intervalEndpoint_mono : Mono intervalEndpoint.{u}.right := by
  have hm : ∀ m, Mono (intervalEndpoint.{u}.right.app m) := by
    intro m
    apply (mono_iff_injective _).2
    intro s t h
    rcases coprod_simplex_cases (𝟙_ SSet.{u}) (𝟙_ SSet.{u}) m s with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases coprod_simplex_cases (𝟙_ SSet.{u}) (𝟙_ SSet.{u}) m t with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact congrArg _ (@Subsingleton.elim PUnit.{u + 1} inferInstance a b)
    · have hh := congrArg (fun z ↦ (stdSimplex.objEquiv z).toOrderHom 0) h
      rw [intervalEndpoint_inl_value, intervalEndpoint_inr_value] at hh
      exact False.elim (by contradiction)
    · have hh := congrArg (fun z ↦ (stdSimplex.objEquiv z).toOrderHom 0) h
      rw [intervalEndpoint_inr_value, intervalEndpoint_inl_value] at hh
      exact False.elim (by contradiction)
    · exact congrArg _ (@Subsingleton.elim PUnit.{u + 1} inferInstance a b)
  exact NatTrans.mono_of_mono_app intervalEndpoint.right

end

end SerrePositivity.KST.Spectra
