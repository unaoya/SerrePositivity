module
public import SerrePositivity.KST.Fibration.CoherentSimplexHomVertices

/-! # 指定 coherent 二単体の合成 path と、全長 path からの実包含辺 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Fibration

/-- 二単体の元の第一短辺の path。 -/
def coherentTriangleFirstPath :
    Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 1) where
  I := {k | k.down ≤ 1}
  left := by decide
  right := by decide
  left_le k _ := Fin.zero_le k.down
  le_right _ hk := hk

/-- 二単体の元の第二短辺の path。 -/
def coherentTriangleLastPath :
    Path (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) where
  I := {k | 1 ≤ k.down}
  left := by decide
  right := by decide
  left_le _ hk := hk
  le_right k _ := Fin.le_last k.down

/-- 指定した二つの短辺の同じ合成 path。 -/
def coherentTriangleFullPath :
    Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) :=
  show (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin 3))) ⟶ ⟨ULift.up 2⟩ from
    coherentTriangleFirstPath ≫ coherentTriangleLastPath

/-- 任意の元の長 path から同じ合成 path への実包含射。 -/
def coherentTrianglePathToFull
    (p : Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) :
    p ⟶ coherentTriangleFullPath := by
  refine ⟨⟨⟨?_⟩⟩⟩
  intro k _hk
  change k.down ≤ 1 ∨ 1 ≤ k.down
  exact le_total k.down 1

/-- 指定した二単体の元の Hom 作用で、path 包含を同じ Kan Hom の実辺へ写す。 -/
def coherentTriangleHomEdge {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌)
    {p q : Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)} (f : p ⟶ q) :
    SSet.Edge (coherentTriangleHomVertex s p) (coherentTriangleHomVertex s q) :=
  (nerve.edgeMk f).map (coherentTriangleLongHom s)

end SerrePositivity.KST.Fibration
