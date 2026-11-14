module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.FunctorTriangleTwoFaces
/-! # 三角形族の全入力輸送と関手単体集合の面

概要：同じ三角形族を入力写像で制限して curry し、その全ての面を保持する。
方針：curry の自然性と tensor 因子の交換だけを使う。
規約：三角形の代表・面・入力写像を変更しない。
使われ方：係数側の六片を主経路の Hom 模型上へ同時に輸送する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

def dgGluingTriangleDiagramTransport {P K Z : SSet.{u}} (a : K ⟶ P)
    (V : (Δ[2] : SSet.{u}) ⊗ P ⟶ Z) : (Δ[2] : SSet.{u}) ⟶ (ihom K).obj Z :=
  curry ((β_ K (Δ[2] : SSet.{u})).hom ≫ (Δ[2] ◁ a) ≫ V)

lemma dgGluingTriangleDiagramTransport_face {P K Z : SSet.{u}} (a : K ⟶ P)
    (V : (Δ[2] : SSet.{u}) ⊗ P ⟶ Z) (d : (Δ[1] : SSet.{u}) ⟶ Δ[2]) :
    d ≫ dgGluingTriangleDiagramTransport a V =
      curry ((a ▷ (Δ[1] : SSet.{u})) ≫ (β_ P (Δ[1] : SSet.{u})).hom ≫ (d ▷ P) ≫ V) := by
  rw [dgGluingTriangleDiagramTransport, ← curry_natural_left]
  apply congrArg curry
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

lemma dgGluingTriangleDiagramTransport_face_eq {P K Z : SSet.{u}} (a : K ⟶ P)
    (V W : (Δ[2] : SSet.{u}) ⊗ P ⟶ Z)
    (d e : (Δ[1] : SSet.{u}) ⟶ Δ[2]) (h : (d ▷ P) ≫ V = (e ▷ P) ≫ W) :
    d ≫ dgGluingTriangleDiagramTransport a V = e ≫ dgGluingTriangleDiagramTransport a W := by
  rw [dgGluingTriangleDiagramTransport_face, dgGluingTriangleDiagramTransport_face, h]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
