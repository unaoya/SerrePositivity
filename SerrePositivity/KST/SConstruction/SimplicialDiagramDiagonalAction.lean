module
public import SerrePositivity.KST.SConstruction.SimplicialDiagramEnrichment
public import SerrePositivity.KST.SConstruction.SSetInternalObject

/-! # 元の対角単体集合への全パラメータ作用
概要：図式全体の標準 end の全単体を、元の対角単体集合に作用させる。
方針：各段の内部 Hom 射影を評価し、添字の自然性と内部の自然性を合成する。
規約：全入力を保持し、Kan 性は課さない。使われ方：反復実現の厳密豊穣化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 同じ元の図式の添字方向と内部方向を同時に対角に取る。 -/
def simplicialSSetDiagramDiagonal (X : SimplicialSSetDiagram.{u}) : SSet.{u} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj X.diagram

/-- 各段の全パラメータ作用は、元の全ての面退化と厳密に可換する。 -/
lemma simplicialSSetDiagramProjection_action_naturality (X Y : SimplicialSSetDiagram.{u})
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    uncurry (simplicialSSetDiagramProjection X Y n) ≫ Y.diagram.map f =
      (X.diagram.map f ▷ (X ⟶[SSet.{u}] Y)) ≫
        uncurry (simplicialSSetDiagramProjection X Y m) := by
  have h := congrArg
    (fun q : (X ⟶[SSet.{u}] Y) ⟶ (ihom (X.diagram.obj n)).obj (Y.diagram.obj m) =>
      uncurry q) (simplicialSSetDiagramProjection_naturality X Y f)
  rw [uncurry_natural_right, uncurry_pre_app] at h
  exact h

/-- 全ての面退化に自然な標準 end の入力族を、元の対角単体集合に作用させる。 -/
def simplicialSSetDiagramDiagonalAction (X Y : SimplicialSSetDiagram.{u}) :
    simplicialSSetDiagramDiagonal X ⊗ (X ⟶[SSet.{u}] Y) ⟶
      simplicialSSetDiagramDiagonal Y where
  app n := ↾fun p => (uncurry (simplicialSSetDiagramProjection X Y n)).app n p
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro p
    have h₁ := congrArg (fun q => q.app n p)
      (simplicialSSetDiagramProjection_action_naturality X Y f)
    have h₂ := CategoryTheory.types_congr_hom
      ((uncurry (simplicialSSetDiagramProjection X Y m)).naturality f)
      ((X.diagram.map f).app n p.1, p.2)
    exact h₂.trans (congrArg (fun x => (Y.diagram.obj m).map f x) h₁.symm)

end SerrePositivity.KST.SConstruction
