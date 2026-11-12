module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ArrowData

/-!
概要：coherent 二単体の三辺と合成を表す path と精密化。
方針：標準の二点 path を面写像で送り、集合の包含を使う。
規約：対象の順序圏は ULift (Fin 3)、Hom の宇宙は u。
使われ方：Cat_∞ の錐の三角形の指定された可換性の読み戻し。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：三角形の最初の辺を表す thickening の path。
方針：二点の標準 path を δ₂ で三点へ送る。
規約：端点は 0 と 1。
使われ方：coherent 二単体の最初の関手の回収。 -/
def coherentTrianglePath01 :
    SimplicialThickening.Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 1) :=
  (SimplicialThickening.functorMap (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap
    ⟨ULift.up (0 : Fin 2)⟩ ⟨ULift.up (1 : Fin 2)⟩).obj _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath
/-- 概要：三角形の後半の辺を表す thickening の path。
方針：二点の標準 path を δ₀ で三点へ送る。
規約：端点は 1 と 2。
使われ方：coherent 二単体の後半の関手の回収。 -/
def coherentTrianglePath12 :
    SimplicialThickening.Path (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) :=
  (SimplicialThickening.functorMap (SimplexCategory.δ (0 : Fin 3)).toOrderHom.uliftMap
    ⟨ULift.up (0 : Fin 2)⟩ ⟨ULift.up (1 : Fin 2)⟩).obj _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath
/-- 概要：三角形の長辺を表す thickening の path。
方針：二点の標準 path を δ₁ で三点へ送る。
規約：端点は 0 と 2、中間の点は含めない。
使われ方：coherent 二単体の長辺の関手の回収。 -/
def coherentTrianglePath02 :
    SimplicialThickening.Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) :=
  (SimplicialThickening.functorMap (SimplexCategory.δ (1 : Fin 3)).toOrderHom.uliftMap
    ⟨ULift.up (0 : Fin 2)⟩ ⟨ULift.up (1 : Fin 2)⟩).obj _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath
/-- 概要：三角形の二辺の合成を表す thickening の path。
方針：最初と後半の path を集合の和で合成する。
規約：中間の頂点 1 を含む。
使われ方：二辺の豊穣合成の回収。 -/
def coherentTriangleCompositePath :
    SimplicialThickening.Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) :=
  (show (⟨ULift.up (0 : Fin 3)⟩ : SimplicialThickening (ULift.{u} (Fin 3))) ⟶
    ⟨ULift.up 1⟩ from coherentTrianglePath01) ≫
      (show (⟨ULift.up (1 : Fin 3)⟩ : SimplicialThickening (ULift.{u} (Fin 3))) ⟶
        ⟨ULift.up 2⟩ from coherentTrianglePath12)
/-- 概要：長辺の path から二辺の合成 path への標準の精密化。
方針：長辺の両端が合成 path に含まれることを示す。
規約：向きは長辺から二辺の合成。
使われ方：coherent 二単体を豊穣 Hom の指定辺へ送る。 -/
def coherentTriangleRefinement : coherentTrianglePath02.{u} ⟶ coherentTriangleCompositePath.{u} :=
  ⟨⟨⟨by
    rintro k ⟨j, hj, rfl⟩
    rcases j with ⟨j⟩
    fin_cases j
    · exact Or.inl coherentTrianglePath01.left
    · exact Or.inr coherentTrianglePath12.right⟩⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
