module
public import SerrePositivity.KST.SConstruction.SimplicialDiagramDiagonalAction
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedActionLaws

/-! # 元の対角作用の単位・合成・通常射の回収
概要：標準 end の全作用を、同じ元の対角で厳密に合成し通常射を回収する。
方針：各段の閉内部 Hom 射影の法則を uncurry し、同じ対角次数で評価する。
規約：対象の Kan 性を要求しない。使われ方：対角実現の厳密単体的豊穣関手。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 元の通常の図式射を、同じ元の対角単体集合の射へ送る。 -/
def simplicialSSetDiagramDiagonalMap {X Y : SimplicialSSetDiagram.{u}} (f : X ⟶ Y) :
    simplicialSSetDiagramDiagonal X ⟶ simplicialSSetDiagramDiagonal Y :=
  Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ)
    (Functor.uncurry.map (show X.diagram ⟶ Y.diagram from f))

private lemma projection_action_unit (X : SimplicialSSetDiagram.{u})
    (n : SimplexCategoryᵒᵖ) :
    (𝟙 (X.diagram.obj n) ⊗ₘ eId SSet.{u} X) ≫
      uncurry (simplicialSSetDiagramProjection X X n) = (ρ_ (X.diagram.obj n)).hom := by
  have h := congrArg
    (fun f : 𝟙_ SSet.{u} ⟶ (ihom (X.diagram.obj n)).obj (X.diagram.obj n) => uncurry f)
      (simplicialSSetDiagramProjection_id X n)
  rw [uncurry_natural_left, MonoidalClosed.id_eq, uncurry_curry] at h
  simpa only [id_tensorHom] using h

private lemma projection_action_comp (X Y Z : SimplicialSSetDiagram.{u})
    (n : SimplexCategoryᵒᵖ) :
    (uncurry (simplicialSSetDiagramProjection X Y n) ⊗ₘ 𝟙 (Y ⟶[SSet.{u}] Z)) ≫
        uncurry (simplicialSSetDiagramProjection Y Z n) =
      (α_ (X.diagram.obj n) (X ⟶[SSet.{u}] Y) (Y ⟶[SSet.{u}] Z)).hom ≫
        (𝟙 (X.diagram.obj n) ⊗ₘ eComp SSet.{u} X Y Z) ≫
          uncurry (simplicialSSetDiagramProjection X Z n) := by
  have h := congrArg
    (fun f : (X ⟶[SSet.{u}] Y) ⊗ (Y ⟶[SSet.{u}] Z) ⟶
      (ihom (X.diagram.obj n)).obj (Z.diagram.obj n) => uncurry f)
      (simplicialSSetDiagramProjection_comp X Y Z n)
  rw [uncurry_natural_left, uncurry_tensor_internalComp] at h
  have hh := congrArg
    ((α_ (X.diagram.obj n) (X ⟶[SSet.{u}] Y) (Y ⟶[SSet.{u}] Z)).hom ≫ ·) h.symm
  simpa only [id_tensorHom, Category.assoc, Iso.hom_inv_id_assoc] using hh

private lemma projection_action_hom {X Y : SimplicialSSetDiagram.{u}} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) :
    (𝟙 (X.diagram.obj n) ⊗ₘ eHomEquiv SSet.{u} f) ≫
      uncurry (simplicialSSetDiagramProjection X Y n) =
        (ρ_ (X.diagram.obj n)).hom ≫ (show X.diagram ⟶ Y.diagram from f).app n := by
  have h := congrArg
    (fun q : 𝟙_ SSet.{u} ⟶ (ihom (X.diagram.obj n)).obj (Y.diagram.obj n) => uncurry q)
      (simplicialSSetDiagramHomEquiv_projection f n)
  rw [uncurry_natural_left, curry', uncurry_curry] at h
  simpa only [id_tensorHom] using h

/-- 元の豊穣恒等入力は、元の対角上でも恒等作用を与える。 -/
lemma simplicialSSetDiagramDiagonalAction_unit (X : SimplicialSSetDiagram.{u}) :
    (𝟙 (simplicialSSetDiagramDiagonal X) ⊗ₘ eId SSet.{u} X) ≫
        simplicialSSetDiagramDiagonalAction X X =
      (ρ_ (simplicialSSetDiagramDiagonal X)).hom := by
  ext n p
  exact congrArg (fun f => f.app n p) (projection_action_unit X n)

/-- 二回の全パラメータ対角作用は、元の標準 end の合成による作用と厳密に一致。 -/
lemma simplicialSSetDiagramDiagonalAction_comp (X Y Z : SimplicialSSetDiagram.{u}) :
    (simplicialSSetDiagramDiagonalAction X Y ⊗ₘ 𝟙 (Y ⟶[SSet.{u}] Z)) ≫
        simplicialSSetDiagramDiagonalAction Y Z =
      (α_ (simplicialSSetDiagramDiagonal X) (X ⟶[SSet.{u}] Y) (Y ⟶[SSet.{u}] Z)).hom ≫
        (𝟙 (simplicialSSetDiagramDiagonal X) ⊗ₘ eComp SSet.{u} X Y Z) ≫
          simplicialSSetDiagramDiagonalAction X Z := by
  ext n p
  exact congrArg (fun f => f.app n p) (projection_action_comp X Y Z n)

/-- 元の通常の図式射に固定すると、元の同じ対角射を全単体で回収する。 -/
lemma simplicialSSetDiagramDiagonalAction_hom {X Y : SimplicialSSetDiagram.{u}}
    (f : X ⟶ Y) :
    (𝟙 (simplicialSSetDiagramDiagonal X) ⊗ₘ eHomEquiv SSet.{u} f) ≫
      simplicialSSetDiagramDiagonalAction X Y =
        (ρ_ (simplicialSSetDiagramDiagonal X)).hom ≫ simplicialSSetDiagramDiagonalMap f := by
  ext n p
  exact congrArg (fun q => q.app n p) (projection_action_hom f n)

end SerrePositivity.KST.SConstruction
