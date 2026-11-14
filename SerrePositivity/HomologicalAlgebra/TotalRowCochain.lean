module

public import SerrePositivity.HomologicalAlgebra.TotalHorizontalHomotopyComponents
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import all SerrePositivity.HomologicalAlgebra.TotalHorizontalHomotopyComponents

/-!
# 非有界全複体のすべての行の指定 cochain

## 概要
横次数 a の同じ直和包含を、次数 a の cochain として記録する。

## 方針
全微分の二成分の公式を使い、cochain の微分で縦の二項を相殺する。

## 規約
有界性は不要。各全次数に必要な直和の存在だけを要求する。

## 使われ方
HA 1.2.4。単体的実現の全次数の成分と strict coherent bar の微分の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Preadditive HomologicalComplex CochainComplex HomComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) [K.HasTotal (.up ℤ)]

/-- 横次数 a の元の直和包含からなる、次数 a の cochain。 -/
def totalRowCochain (a : ℤ) : Cochain (K.X a) (K.total (.up ℤ)) a :=
  Cochain.mk (fun p q h => K.ιTotal (.up ℤ) a p q (by dsimp; omega))

/-- 同じ cochain の各成分は元の同じ直和包含。 -/
@[simp]
theorem totalRowCochain_v (a p q : ℤ) (h : p + a = q) :
    (totalRowCochain K a).v p q h = K.ιTotal (.up ℤ) a p q (by dsimp; omega) := rfl

/-- 全行の指定 cochain の微分は、隣の行への横微分の後の同じ包含。 -/
theorem totalRowCochain_δ_v (a p : ℤ) :
    (δ a (a + 1) (totalRowCochain K a)).v p ((p + a) + 1) (by omega) =
      (K.d a (a + 1)).f p ≫
        K.ιTotal (.up ℤ) (a + 1) p ((p + a) + 1) (by dsimp; omega) := by
  rw [δ_v a (a + 1) rfl _ p ((p + a) + 1) (by omega) (p + a) (p + 1) (by omega) rfl,
    totalRowCochain_v, totalRowCochain_v, ι_totalDifferential]
  simp [ComplexShape.ε, Int.negOnePow_add]

/-- 全行の同じ成分は、二重複体のすべての射に厳密に自然。 -/
theorem totalRowCochain_naturality
    {L : HomologicalComplex₂ C (.up ℤ) (.up ℤ)} [L.HasTotal (.up ℤ)]
    (φ : K ⟶ L) (a p q : ℤ) (h : p + a = q) :
    (totalRowCochain K a).v p q h ≫ (HomologicalComplex₂.total.map φ (.up ℤ)).f q =
      (φ.f a).f p ≫ (totalRowCochain L a).v p q h :=
  K.ιTotal_map L φ (.up ℤ) a p q (by dsimp; omega)

end SerrePositivity.HomologicalAlgebra
