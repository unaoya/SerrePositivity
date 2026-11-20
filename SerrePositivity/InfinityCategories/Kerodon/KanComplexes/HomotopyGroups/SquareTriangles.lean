module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
概要：二つの区間の正方形の二つの三角形と共通の対角辺。
方針：二つの退化写像を組にして三角形の射を構成する。
規約：upper の頂点は (0,0),(0,1),(1,1)、lower は座標を交換したもの。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。二つの円の交換の符号の幾何的比較。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SquareTriangles
end SerrePositivity.KST.Spectra.SquareTriangles
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra.SquareTriangles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：正方形の上側の三角形の単体的な射。
方針：第一成分を σ₀、第二成分を σ₁ とする。
規約：標準二単体を源とする。
使われ方：Goerss–Jardine I §7。正方形の相対写像の一つ目の三角形への制限。 -/
def upper : (Δ[2] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[1] :=
  lift (stdSimplex.σ (0 : Fin 2)) (stdSimplex.σ (1 : Fin 2))

/-- 概要：正方形の下側の三角形の単体的な射。
方針：上側の二つの成分を交換する。
規約：標準二単体を源とする。
使われ方：Goerss–Jardine I §7。正方形の相対写像の二つ目の三角形への制限。 -/
def lower : (Δ[2] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[1] :=
  lift (stdSimplex.σ (1 : Fin 2)) (stdSimplex.σ (0 : Fin 2))

/-- 概要：二つの三角形の共通の対角辺。
方針：二つの区間の恒等射を組にする。
規約：端点は (0,0) と (1,1)。
使われ方：Goerss–Jardine I §7。三角形の写像空間の共通の底。 -/
def diagonal : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[1] := lift (𝟙 _) (𝟙 _)

/-- 概要：上側の三角形の中間の面は対角辺。
方針：二つの射影へ移して面と退化の恒等式を使う。
規約：面の添字は 1。
使われ方：Goerss–Jardine I §7。相対三角形の共通辺の整合。 -/
@[reassoc (attr := simp)]
theorem upper_diagonal : stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.{u} = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.diagonal.{u} := by
  apply CartesianMonoidalCategory.hom_ext
  · change stdSimplex.δ (0 : Fin 2).succ ≫ stdSimplex.σ (0 : Fin 2) = 𝟙 _
    exact CosimplicialObject.δ_comp_σ_succ SSet.stdSimplex
  · change stdSimplex.δ (1 : Fin 2).castSucc ≫ stdSimplex.σ (1 : Fin 2) = 𝟙 _
    exact CosimplicialObject.δ_comp_σ_self SSet.stdSimplex

/-- 概要：下側の三角形の中間の面も同じ対角辺。
方針：二つの射影で面と退化の恒等式を使う。
規約：共通の辺の向きは上側と同じ。
使われ方：Goerss–Jardine I §7。二つの充填の同じ底での比較。 -/
@[reassoc (attr := simp)]
theorem lower_diagonal : stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower.{u} = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.diagonal.{u} := by
  apply CartesianMonoidalCategory.hom_ext
  · change stdSimplex.δ (1 : Fin 2).castSucc ≫ stdSimplex.σ (1 : Fin 2) = 𝟙 _
    exact CosimplicialObject.δ_comp_σ_self SSet.stdSimplex
  · change stdSimplex.δ (0 : Fin 2).succ ≫ stdSimplex.σ (0 : Fin 2) = 𝟙 _
    exact CosimplicialObject.δ_comp_σ_succ SSet.stdSimplex

/-- 概要：正方形の変数の交換は上側と下側の三角形を交換する。
方針：直積の交換を二つの射影で計算する。
規約：通常の単体集合の braiding を使う。
使われ方：Goerss–Jardine I §7。円の二変数の交換を三角形の交換へ移す。 -/
@[reassoc (attr := simp)]
theorem upper_swap : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.{u} ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower.{u} := rfl

/-- 概要：正方形の変数の交換は下側の三角形を上側へ戻す。
方針：直積の交換の二つの射影を計算する。
規約：厳密な射の等式。
使われ方：Goerss–Jardine I §7。符号反転の比較の二方向の制限。 -/
@[reassoc (attr := simp)]
theorem lower_swap : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower.{u} ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.{u} := rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
