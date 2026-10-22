module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeSliceCoconeBoundaryMap
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorVertices

/-!
概要：固定境界への普遍 uncurry の頂点は、元の指定全余錐そのもの。
方針：全関手族の各パラメーターで相対評価と join の比較を計算する。
規約：元の全次数の余錐を保持。使われ方：実相対同型の端点の厳密な同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 普遍全余錐を元の相対頂点へ制限すると、同じ元の全余錐の定値族となる。 -/
lemma relativeSliceCoconeUncurry_vertex {A X : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X) (f : A ⟶ sliceOver p)
    (hf : f ≫ sliceOverProjection p = b) :
    (join A (Δ[0] : SSet.{u}) ◁
      SSet.yonedaEquiv.symm (relativeFunctorVertex (sliceOverProjection p) b f hf)) ≫
        relativeSliceCoconeUncurry p b = fst (join A Δ[0]) Δ[0] ≫ sliceOverUncurry f := by
  let R := relativeFunctorSpace (sliceOverProjection p) b
  let v : (Δ[0] : SSet.{u}) ⟶ R :=
    SSet.yonedaEquiv.symm (relativeFunctorVertex (sliceOverProjection p) b f hf)
  let T := join A (Δ[0] : SSet.{u})
  have hs : (T ◁ v) ≫ (β_ T R).hom = (β_ T Δ[0]).hom ≫ (v ▷ T) := by rfl
  have hv : (v ▷ A) ≫ relativeSliceCoconeLeft p b = snd Δ[0] A ≫ f := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨t, a⟩
    rfl
  have hj : joinMap (v ▷ A) (𝟙 (Δ[0] : SSet.{u})) ≫
      sliceOverUncurry (relativeSliceCoconeLeft p b) =
        joinMap (snd (Δ[0] : SSet.{u}) A) (𝟙 Δ[0]) ≫ sliceOverUncurry f := by
    rw [← sliceOverUncurry_precomp, hv, sliceOverUncurry_precomp]
  change (T ◁ v) ≫ (β_ T R).hom ≫ joinTensorLeft R A Δ[0] ≫
    sliceOverUncurry (relativeSliceCoconeLeft p b) = _
  rw [← Category.assoc (T ◁ v), hs]
  simp only [Category.assoc]
  rw [← Category.assoc (v ▷ T), joinTensorLeft_naturality]
  simp only [Category.assoc]
  rw [hj]
  rw [← Category.assoc (joinTensorLeft (Δ[0] : SSet.{u}) A Δ[0]), joinTensorLeft_unit,
    braiding_hom_snd_assoc]

/-- 元の相対関手の頂点は、元の全余錐を同じ固定境界で表す頂点へ写る。 -/
lemma relativeSliceCoconeBoundaryMap_vertex {A X : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X) (f : A ⟶ sliceOver p)
    (hf : f ≫ sliceOverProjection p = b) :
    (relativeSliceCoconeBoundaryMap p b).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex (sliceOverProjection p) b f hf) =
        fixedCoconeBoundaryVertex p b (sliceOverUncurry f)
          ((sliceOverUncurry_projection f).trans hf) (sliceOverUncurry_fixed f) := by
  apply Subtype.ext
  change (curry (relativeSliceCoconeUncurry p b)).app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex (sliceOverProjection p) b f hf) = functorVertex (sliceOverUncurry f)
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, relativeSliceCoconeUncurry_vertex,
    SSet.yonedaEquiv_symm_zero, uncurry_const_functorVertex]

/-- 相対関手空間の同型は、底と終点を共に固定した元の全余錐の頂点同型へ写る。 -/
def relativeSliceFixedBoundaryIso {A X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X)
    (f g : A ⟶ sliceOver p) (hf : f ≫ sliceOverProjection p = b)
    (hg : g ≫ sliceOverProjection p = b)
    (e : VertexIso (relativeFunctorVertex (sliceOverProjection p) b f hf)
      (relativeFunctorVertex (sliceOverProjection p) b g hg)) :
    VertexIso
      (fixedCoconeBoundaryVertex p b (sliceOverUncurry f)
        ((sliceOverUncurry_projection f).trans hf) (sliceOverUncurry_fixed f))
      (fixedCoconeBoundaryVertex p b (sliceOverUncurry g)
        ((sliceOverUncurry_projection g).trans hg) (sliceOverUncurry_fixed g)) := by
  simpa only [relativeSliceCoconeBoundaryMap_vertex] using
    VertexIso.map e (relativeSliceCoconeBoundaryMap p b)

end SerrePositivity.InfinityCategories.F2.Ind
