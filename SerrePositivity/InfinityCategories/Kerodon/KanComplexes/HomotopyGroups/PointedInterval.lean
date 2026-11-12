module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Heyting.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import SerrePositivity.Spectra.Pointed.SmashMonoidal
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic
public import SerrePositivity.Spectra.PointedSimplicialSet.SmashUnderlying

/-!
概要：始点を基点とする単体的区間と終点の包含。
方針：自由な基点を持つ零次球面から区間への端点射を構成する。
規約：始点は零、終点は一。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の次数移動の path fiber 列。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：始点を基点とする単体的区間。
方針：Δ[1] の頂点零に基点を付ける。
規約：区間自身に Kan 性は要求しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。path space の源。 -/
def pointedInterval : PointedSimplicialSet.{u} :=
  PointedSimplicialSet.ofVertex (Δ[1] : SSet.{u}) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

/-- 概要：零次球面の非基点を区間の終点へ送る。
方針：基点を始点に固定し、自由基点の普遍性を使う。
規約：定義域は点つき smash の単位。
使われ方：Kerodon §3.2.5（Tag 00WD）、Goerss–Jardine I §7。path の終点評価。 -/
def intervalEndpoint : 𝟙_ PointedSimplicialSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} :=
  (PointedSimplicialSet.unitVertexEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval).symm
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

/-- 概要：終点包含の基礎射は二つの端点を指定する余積からの射。
方針：自由基点と頂点の同値の定義を読む。
規約：余積の第一成分が終点、第二成分が基点である始点。
使われ方：Goerss–Jardine I §7。終点包含の単射性。 -/
theorem intervalEndpoint_right : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right =
    coprod.desc (SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := rfl

/-- 概要：単体集合の二項余積の単体は二つの成分のいずれかに属する。
方針：評価関手が余積を保つことと型の余極限の全射性を使う。
規約：任意の単体次数 m。
使われ方：Kerodon §3.1.3（Tag 00TJ）。端点包含の単射性の成分ごとの検査。 -/
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
    (coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.right =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_right, coprod.inl_desc]

/-- 概要：区間の終点射は余積の第二成分を始点へ送る。
方針：余積からの射の第二成分を計算する。
規約：第二成分は基点側。
使われ方：Goerss–Jardine I §7。終点包含の単射性。 -/
@[reassoc (attr := simp)]
theorem intervalEndpoint_inr :
    (coprod.inr : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.right =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_right, coprod.inr_desc]

/-- 概要：終点射の第一成分の像の頂点は一。
方針：定数単体の頂点を計算する。
規約：任意の単体次数 m の先頭頂点で評価する。
使われ方：Kerodon §3.1.3（Tag 00TJ）。両端点の像が交わらないことの検査。 -/
theorem intervalEndpoint_inl_value (m : SimplexCategoryᵒᵖ) (a : (𝟙_ SSet.{u}).obj m) :
    (stdSimplex.objEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.right.app m
      ((coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})).app m a))).toOrderHom 0 = 1 := by
  change (stdSimplex.objEquiv (((coprod.inl : 𝟙_ SSet.{u} ⟶
    (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right).app m a)).toOrderHom 0 = 1
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl]
  rfl

/-- 概要：終点射の第二成分の像の頂点は零。
方針：定数単体の頂点を計算する。
規約：任意の単体次数 m の先頭頂点で評価する。
使われ方：Kerodon §3.1.3（Tag 00TJ）。両端点の像が交わらないことの検査。 -/
theorem intervalEndpoint_inr_value (m : SimplexCategoryᵒᵖ) (a : (𝟙_ SSet.{u}).obj m) :
    (stdSimplex.objEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.right.app m
      ((coprod.inr : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})).app m a))).toOrderHom 0 = 0 := by
  change (stdSimplex.objEquiv (((coprod.inr : 𝟙_ SSet.{u} ⟶
    (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right).app m a)).toOrderHom 0 = 0
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr]
  rfl

/-- 概要：基点と終点を区間へ送る点つき射は単射。
方針：各単体を余積の成分に分け、二端点の像の非交差性を使う。
規約：基礎単体集合の単射性。
使われ方：Kerodon §3.1.3（Tag 00TJ）、Goerss–Jardine I §7。path の終点評価の fibration 性。 -/
instance intervalEndpoint_mono : Mono _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right := by
  have hm : ∀ m, Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right.app m) := by
    intro m
    apply (mono_iff_injective _).2
    intro s t h
    rcases _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.coprod_simplex_cases (𝟙_ SSet.{u}) (𝟙_ SSet.{u}) m s with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.coprod_simplex_cases (𝟙_ SSet.{u}) (𝟙_ SSet.{u}) m t with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact congrArg _ (@Subsingleton.elim PUnit.{u + 1} inferInstance a b)
    · have hh := congrArg (fun z ↦ (stdSimplex.objEquiv z).toOrderHom 0) h
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl_value, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr_value] at hh
      exact False.elim (by contradiction)
    · have hh := congrArg (fun z ↦ (stdSimplex.objEquiv z).toOrderHom 0) h
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr_value, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl_value] at hh
      exact False.elim (by contradiction)
    · exact congrArg _ (@Subsingleton.elim PUnit.{u + 1} inferInstance a b)
  exact NatTrans.mono_of_mono_app _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.right

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.coprod_simplex_cases := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.coprod_simplex_cases

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.intervalEndpoint := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.intervalEndpoint_inl := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.intervalEndpoint_inl_assoc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.intervalEndpoint_inl_value := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl_value

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.intervalEndpoint_inr := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.intervalEndpoint_inr_assoc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.intervalEndpoint_inr_value := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr_value

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_mono (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.intervalEndpoint_mono := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_mono

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.intervalEndpoint_right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_right

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.pointedInterval := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.intervalEndpoint._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.pointedInterval._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval._proof_1
