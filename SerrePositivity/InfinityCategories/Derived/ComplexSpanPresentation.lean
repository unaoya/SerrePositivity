module
public import SerrePositivity.InfinityCategories.DGNerve.ComplexSimplexArrow
public import SerrePositivity.InfinityCategories.Derived.StandardCofiberSquare

/-! # 任意の複体 dg nerve の span の表示

概要：任意の span を三複体と共通の始域を持つ二つの鎖写像で表示する。
方針：二辺の一単体から鎖写像を回収し、始域を等式で合わせる。
規約：HA Example 1.3.1.8。使われ方：指定された全ての span の標準 cofiber。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {S : Type u} [CommRing S]

/-- 始域を等式で同定した鎖写像は同じ一単体を定める。 -/
lemma complexEdge_eqToHom_comp {X Y Z : Complex S} (h : X = Y) (f : Y ⟶ Z) :
    (complexEdge (eqToHom h ≫ f)).edge = (complexEdge f).edge := by
  cases h
  rw [eqToHom_refl, Category.id_comp]

/-- 三複体・二鎖写像による span の表示と元の図式との厳密な一致。 -/
structure ComplexSpanPresentation
    (p : (SSet.horn 2 0 : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) where
  sourceObj : Complex S
  leftObj : Complex S
  rightObj : Complex S
  leftMap : sourceObj ⟶ leftObj
  rightMap : sourceObj ⟶ rightObj
  span_eq : pushoutSpan (standardCofiberSquare leftMap rightMap) = p

/-- 任意の複体 dg nerve の span を通常の鎖写像で表示する。 -/
def presentComplexSpan
    (p : (SSet.horn 2 0 : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) :
    ComplexSpanPresentation p := by
  let s₀ : Simplex S (Complex S) 1 := SSet.yonedaEquiv (SSet.horn₂₀.ι₀₁ ≫ p)
  let s₁ : Simplex S (Complex S) 1 := SSet.yonedaEquiv (SSet.horn₂₀.ι₀₂ ≫ p)
  have he : (dgNerve S (Complex S)).δ 1 s₀ = (dgNerve S (Complex S)).δ 1 s₁ := by
    have H := congrArg (fun f => SSet.yonedaEquiv (f ≫ p)) SSet.horn₂₀.isPushout.w
    simpa only [Category.assoc, SSet.stdSimplex.yonedaEquiv_δ_comp] using H
  have hA : s₀.obj 0 = s₁.obj 0 :=
    congrArg (fun s : Simplex S (Complex S) 0 => s.obj 0) he
  refine ⟨s₀.obj 0, s₀.obj 1, s₁.obj 1, simplexChainMap s₀,
    eqToHom hA ≫ simplexChainMap s₁, ?_⟩
  apply SSet.horn₂₀.isPushout.hom_ext
  · rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_bottomEdge,
      standardCofiberSquare_bottom, complexEdge_simplexChainMap]
    exact SSet.yonedaEquiv.symm_apply_apply _
  · rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge,
      standardCofiberSquare_left, complexEdge_eqToHom_comp, complexEdge_simplexChainMap]
    exact SSet.yonedaEquiv.symm_apply_apply _

end SerrePositivity.InfinityCategories
