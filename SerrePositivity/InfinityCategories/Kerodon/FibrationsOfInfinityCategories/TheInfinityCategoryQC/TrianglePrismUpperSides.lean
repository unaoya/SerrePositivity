module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TrianglePrismFaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TrianglePrismTetrahedra

/-!
概要：三角形の円柱の上側の三つの側面の厳密な同定。
方針：対応する辺のホモトピーの三角形を元の円柱から取り出す。
規約：元の二単体を変更しない。
使われ方：指定三角形の関手同型の比較の整合性。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：辺の比較正方形の上側の三角形。
方針：空間の端と時刻の反対側を退化させる。
規約：元の円柱の二単体を取り、新たな充填を選択しない。
使われ方：錐の各脚の指定比較同型の構成。 -/
def homotopyEdgeTriangleUpper {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y) (t : X _⦋1⦌) :
    Y _⦋2⦌ := H.app (Opposite.op ⦋2⦌)
      (X.σ 0 t, (Δ[1] : SSet.{u}).σ 1 (SSet.yonedaEquiv (𝟙 Δ[1])))
/-- 概要：三角形の円柱の側面は長辺の比較正方形の上側の面。
方針：面と退化の恒等式と時刻座標を計算する。
規約：元の二単体との厳密な等式。
使われ方：三つの四面の合成則を一つの比較式にまとめる。 -/
lemma triangleHomotopyTetrahedron_upper_long {X Y : SSet.{u}}
    (H : X ⊗ Δ[1] ⟶ Y) (s : X _⦋2⦌) :
    Y.δ 2 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron H s 0) = homotopyEdgeTriangleUpper H (X.δ 1 s) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron_face]
  have hx : X.δ 2 (X.σ 0 s) = X.σ 0 (X.δ 1 s) :=
    ConcreteCategory.congr_hom (X.δ_comp_σ_of_gt (show (0 : Fin 2).castSucc < 1 by decide)) s
  have ht : (Δ[1] : SSet.{u}).δ 2 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.trianglePrismTime 0) =
      (Δ[1] : SSet.{u}).σ 1 (SSet.yonedaEquiv (𝟙 Δ[1])) := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  rw [hx, ht]
  rfl
/-- 概要：三角形の円柱の側面は最初の辺の比較正方形の上側の面。
方針：面と退化の恒等式と時刻座標を計算する。
規約：元の二単体との厳密な等式。
使われ方：三つの四面の合成則を一つの比較式にまとめる。 -/
lemma triangleHomotopyTetrahedron_upper_first {X Y : SSet.{u}}
    (H : X ⊗ Δ[1] ⟶ Y) (s : X _⦋2⦌) :
    Y.δ 3 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron H s 0) = homotopyEdgeTriangleUpper H (X.δ 2 s) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron_face]
  have hx : X.δ 3 (X.σ 0 s) = X.σ 0 (X.δ 2 s) :=
    ConcreteCategory.congr_hom (X.δ_comp_σ_of_gt (show (0 : Fin 2).castSucc < 2 by decide)) s
  have ht : (Δ[1] : SSet.{u}).δ 3 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.trianglePrismTime 0) =
      (Δ[1] : SSet.{u}).σ 1 (SSet.yonedaEquiv (𝟙 Δ[1])) := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  rw [hx, ht]
  rfl
/-- 概要：三角形の円柱の側面は最後の辺の比較正方形の上側の面。
方針：面と退化の恒等式と時刻座標を計算する。
規約：元の二単体との厳密な等式。
使われ方：三つの四面の合成則を一つの比較式にまとめる。 -/
lemma triangleHomotopyTetrahedron_upper_last {X Y : SSet.{u}}
    (H : X ⊗ Δ[1] ⟶ Y) (s : X _⦋2⦌) :
    Y.δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron H s 1) = homotopyEdgeTriangleUpper H (X.δ 0 s) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron_face]
  have hx : X.δ 0 (X.σ 1 s) = X.σ 0 (X.δ 0 s) :=
    ConcreteCategory.congr_hom
      (X.δ_comp_σ_of_le (show (0 : Fin 3) ≤ (0 : Fin 2).castSucc by decide)) s
  have ht : (Δ[1] : SSet.{u}).δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.trianglePrismTime 1) =
      (Δ[1] : SSet.{u}).σ 1 (SSet.yonedaEquiv (𝟙 Δ[1])) := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  rw [hx, ht]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
