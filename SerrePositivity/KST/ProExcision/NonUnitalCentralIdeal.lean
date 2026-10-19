module
public import SerrePositivity.KST.ProExcision.NonUnitalSimplicialMaps
public import SerrePositivity.KST.ProExcision.NonUnitalVertexReverse
public import Mathlib.RingTheory.TwoSidedIdeal.Instances

/-!
# 非可換な非単位単体環の実係数イデアル aI

概要：各次数で中心にある指定元の乗法像を実非単位単体環にする。
方針：既証明の実両側イデアルと係数自然性を用い、実包含を構成する。
規約：KST Proposition 4.14 の非可換再記述。I の可換性を要求しない。
使われ方：実 aI→I の ĜL・実アフィン包含と像上の作用。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：指定元の各次数の実像は係数写像に自然。
方針：標準の [n]→[0] と全単体射の実可換性を使う。
規約：KST Proposition 4.14。使われ方：実 aI の係数写像の閉性。 -/
lemma NonUnitalSimplicialRing.vertexValue_natural (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) {k l : SimplexCategoryᵒᵖ} (φ : k ⟶ l) :
    I.map φ (I.vertexValue a k) = I.vertexValue a l := by
  have h := congrArg (fun f : I.obj (op ⦋0⦌) →ₙ+* I.obj l ↦ f a)
    (I.map_comp (simplexVertexMap k) φ).symm
  rw [simplexVertexMap_comp] at h
  exact h

/-- 概要：各次数で中心にある指定元の実乗法像の非単位単体環。
方針：実両側イデアルを各対象とし、実係数準同型を制限する。
規約：KST Proposition 4.14 の非可換再記述 aI。各次数の中心性を明示する。
使われ方：実係数包含と実一般線形モノイドの始域。 -/
def NonUnitalSimplicialRing.centralIdeal (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (ha : ∀ k, IsCentralElement (I.vertexValue a k)) :
    NonUnitalSimplicialRing.{u} where
  obj k := NonUnitalRingObject.of (centralMultiplicationIdeal (I.vertexValue a k) (ha k))
  map {k l} φ := {
    toFun := fun x ↦ ⟨I.map φ x.val, centralMultiplicationIdeal_map_mem (I.map φ)
      (I.vertexValue a k) (I.vertexValue a l) (ha k) (ha l) (I.vertexValue_natural a φ) x.property⟩
    map_zero' := Subtype.ext (map_zero _)
    map_add' x y := Subtype.ext (map_add _ x.val y.val)
    map_mul' x y := Subtype.ext (map_mul _ x.val y.val) }
  map_id k := by
    apply NonUnitalRingHom.ext
    intro x
    apply Subtype.ext
    change I.map (𝟙 k) x.val = x.val
    rw [I.map_id]
    rfl
  map_comp {k l s} φ ψ := by
    apply NonUnitalRingHom.ext
    intro x
    apply Subtype.ext
    change I.map (φ ≫ ψ) x.val = I.map ψ (I.map φ x.val)
    rw [I.map_comp]
    rfl

/-- 概要：実係数イデアル aI から元の非単位単体環への実包含。
方針：各次数の実両側イデアルの標準包含を全単体射に自然に束ねる。
規約：KST Proposition 4.14。使われ方：実 aI→I の ĜL と像上の作用。 -/
def NonUnitalSimplicialRing.centralIdealInclusion (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (ha : ∀ k, IsCentralElement (I.vertexValue a k)) :
    NonUnitalSimplicialRingHom (I.centralIdeal a ha) I where
  app k := NonUnitalSubringClass.subtype (centralMultiplicationIdeal (I.vertexValue a k) (ha k))
  naturality φ := rfl

end SerrePositivity.KST.ProExcision
