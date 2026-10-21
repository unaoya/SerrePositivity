module

public import SerrePositivity.EInfinity.Hammock.RelativeFixedZigzagFunctor
public import SerrePositivity.EInfinity.SimplicialLocalization.RelativeCategory

/-!
# 相対圏の図式の固定対象の zigzag 圏

概要：全作用素で対象の表示を保つ相対圏の図式から、固定語の zigzag 圏の図式を得る。
方針：各相対関手を、元の端点の等式移送を含む固定 zigzag 関手へ移す。
規約：元の全対象・全射と恒等・合成則を保持する。
使われ方：自由相対解像の固定した両対象の hammock 図式。
-/

@[expose] public section
universe u uI vI uO
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
open CategoryTheory SimplicialLocalization

variable {I : Type uI} [Category.{vI} I] (D : I ⥤ RelativeCategory.{u}) {O : Type uO}
  (p : (i : I) → O → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : O), (D.map θ).functor.obj (p i X) = p j X)

def zigzagDiagram (w : Word) (X Y : O) : I ⥤ Cat.{u, u} where
  obj i := Cat.of (Zigzag (D.obj i).weakEquivalences w (p i X) (p i Y))
  map θ := (Zigzag.Relative.fixedFunctor (D.map θ) (hp θ X) (hp θ Y)).toCatHom
  map_id i := by
    apply Cat.Hom.ext
    have h : (D.map (𝟙 i)).functor =
        (LocalizerMorphism.id (D.obj i).weakEquivalences).functor :=
      congrArg (fun F : D.obj i ⟶ D.obj i => F.functor) (D.map_id i)
    exact (Zigzag.Relative.fixedFunctor_congr h (hp (𝟙 i) X) (hp (𝟙 i) Y) rfl rfl).trans
      (Zigzag.Relative.fixedFunctor_id rfl rfl)
  map_comp {i j k} θ φ := by
    apply Cat.Hom.ext
    have h : (D.map (θ ≫ φ)).functor = ((D.map θ).comp (D.map φ)).functor :=
      congrArg (fun F : D.obj i ⟶ D.obj k => F.functor) (D.map_comp θ φ)
    exact (Zigzag.Relative.fixedFunctor_congr h (hp (θ ≫ φ) X) (hp (θ ≫ φ) Y)
      ((congrArg (D.map φ).functor.obj (hp θ X)).trans (hp φ X))
      ((congrArg (D.map φ).functor.obj (hp θ Y)).trans (hp φ Y))).trans
        (Zigzag.Relative.fixedFunctor_comp (D.map θ) (D.map φ)
          (hp θ X) (hp θ Y) (hp φ X) (hp φ Y))

def graphDiagram (w : Word) (X Y : O) : I ⥤ SSet.{u} :=
  zigzagDiagram D p hp w X Y ⋙ nerveFunctor

end SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
