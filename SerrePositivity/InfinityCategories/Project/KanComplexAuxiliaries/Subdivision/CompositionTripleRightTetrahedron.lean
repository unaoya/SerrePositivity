module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CompositionTripleTetrahedron

/-! # 元の三面を保持する右結合の実四面体
概要：前後二射の合成面と左結合面を全体として保持し、右結合の面を取り出す。
方針：同じ三つの全二面を第二内ホーンへ貼る。
規約：元の全三面を保持し、独立な第四面の一致は主張しない。
使われ方：十二面の六対角面の消去を、実四面体の結合替えへ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 前後二射と左結合の元の三面を保持する実四面体。 -/
structure CompositionTripleRightTetrahedron {E : SSet.{u}} {w x y z : E _⦋0⦌}
    {a : E.Edge w x} {b : E.Edge x y} {c : E.Edge y z}
    {ab : E.Edge w y} {bc : E.Edge x z} {abc : E.Edge w z}
    (first : SSet.Edge.CompStruct a b ab)
    (second : SSet.Edge.CompStruct b c bc)
    (left : SSet.Edge.CompStruct ab c abc) where
  /-- 元の全三面を持つ同じ実三単体。 -/
  simplex : E _⦋3⦌
  /-- 後の二射の元の全合成面。 -/
  second_face : E.δ 0 simplex = second.simplex
  /-- 左結合の元の全合成面。 -/
  left_face : E.δ 1 simplex = left.simplex
  /-- 前の二射の元の全合成面。 -/
  first_face : E.δ 3 simplex = first.simplex
  /-- 同じ四面体の右結合の実合成面。 -/
  right : SSet.Edge.CompStruct a bc abc
  /-- 新しい面も同じ実四面体の面そのもの。 -/
  right_face : right.simplex = E.δ 2 simplex

/-- 元の全三面を持つ指定済みの全三単体を、同じ実結合替えデータとして回収する。 -/
def compositionTripleRightTetrahedronOfMap {E : SSet.{u}}
    {w x y z : E _⦋0⦌} {a : E.Edge w x} {b : E.Edge x y} {c : E.Edge y z}
    {ab : E.Edge w y} {bc : E.Edge x z} {abc : E.Edge w z}
    (first : SSet.Edge.CompStruct a b ab)
    (second : SSet.Edge.CompStruct b c bc)
    (left : SSet.Edge.CompStruct ab c abc)
    (s : (Δ[3] : SSet.{u}) ⟶ E)
    (hs₀ : stdSimplex.δ 0 ≫ s = SSet.yonedaEquiv.symm second.simplex)
    (hs₁ : stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm left.simplex)
    (hs₃ : stdSimplex.δ 3 ≫ s = SSet.yonedaEquiv.symm first.simplex)
    : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron first second left := by
  let σ := SSet.yonedaEquiv s
  have h₀ : E.δ 0 σ = second.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hs₀, Equiv.apply_symm_apply]
  have h₁ : E.δ 1 σ = left.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hs₁, Equiv.apply_symm_apply]
  have h₃ : E.δ 3 σ = first.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hs₃, Equiv.apply_symm_apply]
  have hd₂ : E.δ 2 (E.δ 2 σ) = a.edge := by
    have he := ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_δ_self E (n := 1) (i := 2)) σ
    exact (he.trans (congrArg (E.δ 2) h₃)).trans first.d₂
  have hd₀ : E.δ 0 (E.δ 2 σ) = bc.edge := by
    exact ((E.δ_comp_δ_apply (i := (0 : Fin 3)) (j := 1) (by decide) σ).trans
      (congrArg (E.δ 1) h₀)).trans second.d₁
  have hd₁ : E.δ 1 (E.δ 2 σ) = abc.edge := by
    have he := ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_δ_self E (n := 1) (i := 1)) σ
    exact (he.symm.trans (congrArg (E.δ 1) h₁)).trans left.d₁
  exact ⟨σ, h₀, h₁, h₃, SSet.Edge.CompStruct.mk (E.δ 2 σ) hd₂ hd₀ hd₁, rfl⟩

/-- 元の全三面を保持した第二内ホーンを埋め、同じ四面体の右結合面を得る。 -/
def compositionTripleRightTetrahedron {E : SSet.{u}} [Quasicategory E]
    {w x y z : E _⦋0⦌} {a : E.Edge w x} {b : E.Edge x y} {c : E.Edge y z}
    {ab : E.Edge w y} {bc : E.Edge x z} {abc : E.Edge w z}
    (first : SSet.Edge.CompStruct a b ab)
    (second : SSet.Edge.CompStruct b c bc)
    (left : SSet.Edge.CompStruct ab c abc) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron first second left := by
  let horn := horn₃₂.exists_desc (SSet.yonedaEquiv.symm second.simplex)
    (SSet.yonedaEquiv.symm left.simplex) (SSet.yonedaEquiv.symm first.simplex)
    (by simp) (by simp) (by simp)
  let fill := Quasicategory.hornFilling (by decide) (by decide) horn.choose
  let s := fill.choose
  have hs₀ : stdSimplex.δ 0 ≫ s = SSet.yonedaEquiv.symm second.simplex := by
    have he := congrArg (· ≫ s) (SSet.horn.ι_ι (2 : Fin 4) 0 (by decide)).symm
    exact he.trans ((Category.assoc _ _ _).trans
      ((congrArg (SSet.horn.ι (2 : Fin 4) 0 (by decide) ≫ ·) fill.choose_spec.symm).trans
        horn.choose_spec.1))
  have hs₁ : stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm left.simplex := by
    have he := congrArg (· ≫ s) (SSet.horn.ι_ι (2 : Fin 4) 1 (by decide)).symm
    exact he.trans ((Category.assoc _ _ _).trans
      ((congrArg (SSet.horn.ι (2 : Fin 4) 1 (by decide) ≫ ·) fill.choose_spec.symm).trans
        horn.choose_spec.2.1))
  have hs₃ : stdSimplex.δ 3 ≫ s = SSet.yonedaEquiv.symm first.simplex := by
    have he := congrArg (· ≫ s) (SSet.horn.ι_ι (2 : Fin 4) 3 (by decide)).symm
    exact he.trans ((Category.assoc _ _ _).trans
      ((congrArg (SSet.horn.ι (2 : Fin 4) 3 (by decide) ≫ ·) fill.choose_spec.symm).trans
        horn.choose_spec.2.2))
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compositionTripleRightTetrahedronOfMap first second left s hs₀ hs₁ hs₃

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
