module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconePointHomSquare
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHomotopyEdges

/-!
概要：余錐の二つの時間と図式・Hom のパラメータを、標準三角形の入力の順へ並べる。
方針：次数ごとの四つの直積成分を交換する。
規約：時間の順は図式から頂点、続いて全 Hom の輸送。
使われ方：元の余錐の正方形を標準三角形へ制限する。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：二つの時間を先に並べた入力を余錐の正方形の入力へ移す。
方針：四成分の並べ替え。規約：時間の順は保持。使われ方：三角形の族。 -/
def coconeSquareParameters (K T : SSet.{u}) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ (K ⊗ T) ⟶
      (K ⊗ (Δ[1] : SSet.{u})) ⊗ (T ⊗ (Δ[1] : SSet.{u})) where
  app _ := ↾fun a ↦ ((a.2.1, a.1.1), (a.2.2, a.1.2))
  naturality {_ _} _ := rfl

/-- 概要：一つ目の時間と元の図式・Hom のパラメータを円柱の順へ移す。
方針：三成分の並べ替え。規約：全単体で自然。使われ方：三角形の第一辺。 -/
def coconeHorizontalParameters (K T : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (K ⊗ T) ⟶ (K ⊗ (Δ[1] : SSet.{u})) ⊗ T where
  app _ := ↾fun a ↦ ((a.2.1, a.1), a.2.2)
  naturality {_ _} _ := rfl

/-- 概要：二つ目の時間を全 Hom パラメータとまとめる。
方針：三成分の並べ替え。規約：元の図式の成分を保持。使われ方：三角形の第二辺。 -/
def coconeVerticalParameters (K T : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (K ⊗ T) ⟶ K ⊗ (T ⊗ (Δ[1] : SSet.{u})) where
  app _ := ↾fun a ↦ (a.2.1, (a.2.2, a.1))
  naturality {_ _} _ := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
