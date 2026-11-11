module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.RightHomotopySquare
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyDiagram

/-!
概要：実二単体の三辺を、終辺が定値である同じ係数四角形で読む。
方針：既存の右ホモトピー正方形の折り畳みを全係数と直積する。
規約：三辺と全係数を厳密に保持。使われ方：高次実図式の三角形面の指定比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ係数を保ち、四角形の最終辺を二単体の最終頂点へ畳む射。 -/
def transportTriangleParameter (P : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ P) ⟶ Δ[2] ⊗ P :=
  (α_ (Δ[1] : SSet.{u}) Δ[1] P).inv ≫ (rightHomotopySquare ▷ P)

/-- 外側の零端は、元の二単体の第一辺。 -/
lemma transportTriangleParameter_bottom (P : SSet.{u}) :
    prismEndpoint 0 _ ≫ transportTriangleParameter P = stdSimplex.δ (2 : Fin 3) ▷ P := by
  rw [transportTriangleParameter, ← Category.assoc, prismEndpoint_associator_inv,
    ← comp_whiskerRight, rightHomotopySquare_source]

/-- 外側の一端は、元の二単体の最終頂点を全係数で固定する。 -/
lemma transportTriangleParameter_top (P : SSet.{u}) :
    prismEndpoint 1 _ ≫ transportTriangleParameter P =
      (SSet.const (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) ▷ P) := by
  rw [transportTriangleParameter, ← Category.assoc, prismEndpoint_associator_inv,
    ← comp_whiskerRight, rightHomotopySquare_target]

/-- 内側の零端は、元の二単体の長辺。 -/
lemma transportTriangleParameter_left (P : SSet.{u}) :
    ((Δ[1] : SSet.{u}) ◁ prismEndpoint 0 P) ≫ transportTriangleParameter P =
      stdSimplex.δ (1 : Fin 3) ▷ P := by
  have hp : ((Δ[1] : SSet.{u}) ◁ prismEndpoint 0 P) ≫ (α_ Δ[1] Δ[1] P).inv =
      SSet.ι₀ ▷ P := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [transportTriangleParameter, ← Category.assoc, hp, ← comp_whiskerRight,
    rightHomotopySquare_zero]

/-- 内側の一端は、元の二単体の第二辺。 -/
lemma transportTriangleParameter_right (P : SSet.{u}) :
    ((Δ[1] : SSet.{u}) ◁ prismEndpoint 1 P) ≫ transportTriangleParameter P =
      stdSimplex.δ (0 : Fin 3) ▷ P := by
  have hp : ((Δ[1] : SSet.{u}) ◁ prismEndpoint 1 P) ≫ (α_ Δ[1] Δ[1] P).inv =
      SSet.ι₁ ▷ P := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [transportTriangleParameter, ← Category.assoc, hp, ← comp_whiskerRight,
    rightHomotopySquare_one]

/-- 畳んだ終辺は、時間を忘れて元の二単体の実最終頂点を読む射。 -/
lemma transportTriangleParameter_top_factor (P : SSet.{u}) :
    prismEndpoint 1 _ ≫ transportTriangleParameter P =
      CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) P ≫
        (prismEndpoint 1 P ≫ (stdSimplex.δ (1 : Fin 3) ▷ P)) := by
  rw [transportTriangleParameter_top]
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
