module


public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# 単体集合の余積の包含の単射性

概要：単体集合の二項余積の包含は単射である。
方針：各次数で評価すると型の余積の包含になることを余極限保存で確認する。
規約：Segal 1974 Lemma 1.7 の貼り合わせの単射の補助。
使われ方：二項余積の射を単射に沿う pushout として扱う。
-/

@[expose] public section
universe u
namespace SerrePositivity.KST.Comparison
end SerrePositivity.KST.Comparison
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：任意の二項余積の包含が単射となる MonoCoprod 構造を単体集合に与える。
方針：次数での評価が二項余積を保ち、型の余積の包含が単射であることを使う。
規約：特定の余積の実装に依存せず、任意の余極限の cofan について証明する。
使われ方：余積の比較射の局所化可逆性。
-/
instance simplicialMonoCoprod : MonoCoprod SSet.{u} where
  binaryCofan_inl {A B} c hc := by
    rw [NatTrans.mono_iff_mono_app]
    intro d
    let F := (evaluation SimplexCategoryᵒᵖ (Type u)).obj d
    exact MonoCoprod.binaryCofan_inl (c.map F)
      ((BinaryCofan.isColimitMapConeEquiv (F := F)) (isColimitOfPreserves F hc))

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
