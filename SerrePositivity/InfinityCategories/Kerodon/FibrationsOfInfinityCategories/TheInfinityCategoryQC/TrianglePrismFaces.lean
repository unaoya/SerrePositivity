module
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TrianglePrismTetrahedra
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：三角形の円柱を構成する三単体の共有面と上下の面。
方針：円柱の自然性と面・退化の恒等式を使う。
規約：ホモトピー類だけでなく二単体そのものを同定する。
使われ方：錐の三角形の指定関手同型の比較。

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

/-- 概要：三角形の円柱の三単体の各面の式。
方針：円柱上の射の自然性を適用する。
規約：二単体そのものの厳密な等式。
使われ方：全錐の比較円柱への四面の合成則の適用。 -/
lemma triangleHomotopyTetrahedron_face {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y)
    (s : X _⦋2⦌) (i : Fin 3) (j : Fin 4) :
    Y.δ j (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron H s i) =
      H.app (Opposite.op ⦋2⦌)
        (X.δ j (X.σ i s), (Δ[1] : SSet.{u}).δ j (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.trianglePrismTime i)) := by
  exact (ConcreteCategory.congr_hom (H.naturality (SimplexCategory.δ j).op)
    (show (X ⊗ Δ[1]) _⦋3⦌ from (X.σ i s, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.trianglePrismTime i))).symm
/-- 概要：最初と中央の三単体の共有面は同じ二単体。
方針：面と退化の恒等式と時刻の一致を使う。
規約：二単体そのものの厳密な等式。
使われ方：全錐の比較円柱への四面の合成則の適用。 -/
lemma triangleHomotopyTetrahedron_glue_first {X Y : SSet.{u}}
    (H : X ⊗ Δ[1] ⟶ Y) (s : X _⦋2⦌) :
    Y.δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron H s 0) =
      Y.δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron H s 1) := by
  rw [triangleHomotopyTetrahedron_face, triangleHomotopyTetrahedron_face]
  have h₀ : X.δ 1 (X.σ 0 s) = s :=
    ConcreteCategory.congr_hom (X.δ_comp_σ_succ (i := (0 : Fin 3))) s
  have h₁ : X.δ 1 (X.σ 1 s) = s :=
    ConcreteCategory.congr_hom (X.δ_comp_σ_self (i := (1 : Fin 3))) s
  rw [h₀, h₁, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.trianglePrismTime_glue_first]
/-- 概要：中央と最後の三単体の共有面は同じ二単体。
方針：面と退化の恒等式と時刻の一致を使う。
規約：二単体そのものの厳密な等式。
使われ方：全錐の比較円柱への四面の合成則の適用。 -/
lemma triangleHomotopyTetrahedron_glue_last {X Y : SSet.{u}}
    (H : X ⊗ Δ[1] ⟶ Y) (s : X _⦋2⦌) :
    Y.δ 2 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron H s 1) =
      Y.δ 2 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron H s 2) := by
  rw [triangleHomotopyTetrahedron_face, triangleHomotopyTetrahedron_face]
  have h₁ : X.δ 2 (X.σ 1 s) = s :=
    ConcreteCategory.congr_hom (X.δ_comp_σ_succ (i := (1 : Fin 3))) s
  have h₂ : X.δ 2 (X.σ 2 s) = s :=
    ConcreteCategory.congr_hom (X.δ_comp_σ_self (i := (2 : Fin 3))) s
  rw [h₁, h₂, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.trianglePrismTime_glue_last]
/-- 概要：最初の三単体の上面は終端の三角形の像。
方針：時刻一の端点条件を使う。
規約：二単体そのものの厳密な等式。
使われ方：全錐の比較円柱への四面の合成則の適用。 -/
lemma triangleHomotopyTetrahedron_first {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (s : X _⦋2⦌) :
    Y.δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron H.h s 0) = g.app (Opposite.op ⦋2⦌) s := by
  rw [triangleHomotopyTetrahedron_face]
  have h₀ : X.δ 0 (X.σ 0 s) = s :=
    ConcreteCategory.congr_hom (X.δ_comp_σ_self (i := (0 : Fin 3))) s
  rw [h₀, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.trianglePrismTime_first]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app H.h₁ (Opposite.op ⦋2⦌)) s
/-- 概要：最後の三単体の下面は始端の三角形の像。
方針：時刻零の端点条件を使う。
規約：二単体そのものの厳密な等式。
使われ方：全錐の比較円柱への四面の合成則の適用。 -/
lemma triangleHomotopyTetrahedron_last {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (s : X _⦋2⦌) :
    Y.δ 3 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron H.h s 2) = f.app (Opposite.op ⦋2⦌) s := by
  rw [triangleHomotopyTetrahedron_face]
  have h₂ : X.δ 3 (X.σ 2 s) = s :=
    ConcreteCategory.congr_hom (X.δ_comp_σ_succ (i := (2 : Fin 3))) s
  rw [h₂, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.trianglePrismTime_last]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app H.h₀ (Opposite.op ⦋2⦌)) s

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
