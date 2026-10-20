module
public import SerrePositivity.KST.SConstruction.KanMappingComposition

/-! # 元の合成三角形と指定比較面を保つ合成辺の置換
概要：元の合成面と、長辺を指定射へ比較する実三角形を同じ四面体の面に保持する。
方針：共有する恒等辺を含む内ホーンを貼り、残る実合成面を取り出す。
規約：元の指定比較面を類の等式に置換せず、全二単体を厳密に保持する。
使われ方：元の BF 境界比較を coherent nerve の実合成三角形へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 元の合成面と指定比較面を同時に保持する実四面体と新しい合成面。 -/
structure CompositionReplacementTetrahedron {E : SSet.{u}} {x y z : E _⦋0⦌}
    {a : E.Edge x y} {b : E.Edge y z} {c h : E.Edge x z}
    (original : SSet.Edge.CompStruct a b c)
    (replacement : SSet.Edge.CompStruct (SSet.Edge.id x) c h) where
  /-- 元の全三面を保持する実三単体。 -/
  simplex : E _⦋3⦌
  /-- 元の二射の合成三角形。 -/
  original_face : E.δ 0 simplex = original.simplex
  /-- 元の指定比較三角形。 -/
  replacement_face : E.δ 2 simplex = replacement.simplex
  /-- 共通の恒等辺を持つ同じ退化三角形。 -/
  unit_face : E.δ 3 simplex = (SSet.Edge.CompStruct.idComp a).simplex
  /-- 元の二辺と指定された長辺を持つ実合成面。 -/
  triangle : SSet.Edge.CompStruct a b h
  /-- 新しい面も同じ実四面体の面そのもの。 -/
  triangle_face : triangle.simplex = E.δ 1 simplex

/-- 元の全合成面・全指定比較面を保持して、同じ四面体の実合成面を構成する。 -/
def compositionReplacementTetrahedron {E : SSet.{u}} [Quasicategory E]
    {x y z : E _⦋0⦌} {a : E.Edge x y} {b : E.Edge y z} {c h : E.Edge x z}
    (original : SSet.Edge.CompStruct a b c)
    (replacement : SSet.Edge.CompStruct (SSet.Edge.id x) c h) :
    CompositionReplacementTetrahedron original replacement := by
  let unit := SSet.Edge.CompStruct.idComp a
  let horn := horn₃₁.exists_desc (SSet.yonedaEquiv.symm original.simplex)
    (SSet.yonedaEquiv.symm replacement.simplex) (SSet.yonedaEquiv.symm unit.simplex)
    (by simp) (by simp) (by simp)
  let fill := Quasicategory.hornFilling (by decide) (by decide) horn.choose
  let s := fill.choose
  have hs₀ : stdSimplex.δ 0 ≫ s = SSet.yonedaEquiv.symm original.simplex := by
    have he := congrArg (· ≫ s) (SSet.horn.ι_ι (1 : Fin 4) 0 (by decide)).symm
    exact he.trans ((Category.assoc _ _ _).trans
      ((congrArg (SSet.horn.ι (1 : Fin 4) 0 (by decide) ≫ ·) fill.choose_spec.symm).trans
        horn.choose_spec.1))
  have hs₂ : stdSimplex.δ 2 ≫ s = SSet.yonedaEquiv.symm replacement.simplex := by
    have he := congrArg (· ≫ s) (SSet.horn.ι_ι (1 : Fin 4) 2 (by decide)).symm
    exact he.trans ((Category.assoc _ _ _).trans
      ((congrArg (SSet.horn.ι (1 : Fin 4) 2 (by decide) ≫ ·) fill.choose_spec.symm).trans
        horn.choose_spec.2.1))
  have hs₃ : stdSimplex.δ 3 ≫ s = SSet.yonedaEquiv.symm unit.simplex := by
    have he := congrArg (· ≫ s) (SSet.horn.ι_ι (1 : Fin 4) 3 (by decide)).symm
    exact he.trans ((Category.assoc _ _ _).trans
      ((congrArg (SSet.horn.ι (1 : Fin 4) 3 (by decide) ≫ ·) fill.choose_spec.symm).trans
        horn.choose_spec.2.2))
  let σ := SSet.yonedaEquiv s
  have h₀ : E.δ 0 σ = original.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hs₀, Equiv.apply_symm_apply]
  have h₂ : E.δ 2 σ = replacement.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hs₂, Equiv.apply_symm_apply]
  have h₃ : E.δ 3 σ = unit.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hs₃, Equiv.apply_symm_apply]
  let T : SSet.Edge.CompStruct a b h := SSet.Edge.CompStruct.mk (E.δ 1 σ)
    (SSet.yonedaEquiv.symm.injective (by
      simp [σ, ← stdSimplex.δ_comp_yonedaEquiv_symm,
        ← dsimp% stdSimplex.δ_comp_δ_assoc (n := 1) (i := 1) (j := 2) (by simp), hs₃]))
    (SSet.yonedaEquiv.symm.injective (by
      simp [σ, ← stdSimplex.δ_comp_yonedaEquiv_symm,
        dsimp% stdSimplex.δ_comp_δ_assoc (n := 1) (i := 0) (j := 0) (by simp), hs₀]))
    (SSet.yonedaEquiv.symm.injective (by
      simp [σ, ← stdSimplex.δ_comp_yonedaEquiv_symm,
        dsimp% stdSimplex.δ_comp_δ_self_assoc (i := 1), hs₂]))
  exact ⟨σ, h₀, h₂, h₃, T, rfl⟩

end SerrePositivity.KST.SConstruction
