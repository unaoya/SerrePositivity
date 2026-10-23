module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedTriangleFiberRestriction

/-!
概要：底の指定点を被覆する任意の始域射で元の全 pointed 三角形を制限する。
方針：一点パラメータを代入し、底の定値条件を全二単体へ適用する。
規約：全二単体を保持。使われ方：小さい fiber から元の全三角形への制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定点を被覆する始域射へ一点パラメータを付けた射は底でも同じ点に定値。 -/
lemma sourceParameterPoint_projection {E B C : SSet.{u + 1}}
    (p : E ⟶ B) (b : B _⦋0⦌) (s : C ⟶ E) (hs : s ≫ p = SSet.const b) :
    lift s (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
        (p ▷ (Δ[0] : SSet.{u + 1})) =
      SSet.const (b, stdSimplex.obj₀Equiv.symm (0 : Fin 1)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, lift_fst, hs]
    rfl
  · rw [Category.assoc, whiskerRight_snd, lift_snd]
    rfl

/-- 任意の同じ点を被覆する始域で制限した全三角形の底は元の指定一点評価。 -/
lemma pointedTriangleSourceRestriction_projection {E B C : SSet.{u + 1}}
    (p : E ⟶ B) (b : B _⦋0⦌) (s : C ⟶ E) (hs : s ≫ p = SSet.const b)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ (Δ[0] : SSet.{u + 1})) ⟶ SpaceInfinity.{u})
    (L : (Δ[2] : SSet.{u + 1}) ⊗ (E ⊗ (Δ[0] : SSet.{u + 1})) ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = (Δ[2] ◁ (p ▷ (Δ[0] : SSet.{u + 1}))) ≫ H) :
    (Δ[2] ◁ lift s (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫
      L ≫ pointedSpaceProjection =
        fst (Δ[2] : SSet.{u + 1}) C ≫ coherentTransformationPointDiagram H b := by
  rw [hL, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    sourceParameterPoint_projection p b s hs]
  rfl

end SerrePositivity.InfinityCategories.F2
