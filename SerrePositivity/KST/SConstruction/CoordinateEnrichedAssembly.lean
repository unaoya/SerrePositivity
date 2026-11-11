module
public import SerrePositivity.KST.SConstruction.SimplicialEnrichedDiagramFunctor
public import SerrePositivity.KST.SConstruction.DiagonalParameterizedEvaluation
public import SerrePositivity.KST.SConstruction.MultiDiagonalAssembly

/-! # 元の区間組み立ての全入力族自然性
概要：全多単体比較を保持する図式の対角作用は、元の区間組み立てと可換する。
方針：標準 end の射影で各段の作用を回収し、組み立ての添字の比較を評価する。
規約：全高次パラメータを保持する。使われ方：隣接する反復 K 段の構造写像。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {J : Type w} [Category J]

/-- 元の図式を任意の単体的添字で対角に制限した全入力族の作用。 -/
def coordinateEnrichedDiagonalAction
    (D : J ⥤ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory C) (I : SimplexCategoryᵒᵖ ⥤ J)
    (X Y : C) :
    simplicialDiagonalFunctor.obj
      (I ⋙ D ⋙ quasicategoryEnrichedEvaluationFunctor X ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) ⊗
        (X ⟶[SSet.{u}] Y) ⟶
    simplicialDiagonalFunctor.obj
      (I ⋙ D ⋙ quasicategoryEnrichedEvaluationFunctor Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) :=
  uncurry ((simplicialEnrichedDiagramFunctor (I ⋙ D)).map X Y ≫
    simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _)

/-- 全対角作用は、各次数で元の同じ段の全入力族の作用を回収する。 -/
lemma coordinateEnrichedDiagonalAction_app
    (D : J ⥤ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory C) (I : SimplexCategoryᵒᵖ ⥤ J)
    (X Y : C) (n : SimplexCategoryᵒᵖ)
    (x : (((D.obj (I.obj n)).obj X).obj).obj n) (p : (X ⟶[SSet.{u}] Y).obj n) :
    (coordinateEnrichedDiagonalAction D I X Y).app n (x, p) =
      (uncurry ((D.obj (I.obj n)).map X Y)).app n (x, p) := by
  have h := congrArg (uncurry (C := SSet.{u}))
    (simplicialEnrichedDiagramFunctor_projection (I ⋙ D) X Y n)
  exact (simplicialSSetDiagramDiagonal_parameter_app
    ((simplicialEnrichedDiagramFunctor (I ⋙ D)).map X Y) n x p).trans
      (congrArg (fun q => q.app n (x, p)) h)

/-- 元の区間組み立ては、全高次入力族による対角作用と厳密に可換する。 -/
lemma coordinateDiagonalAssembly_enriched_naturality (r : ℕ)
    (D : (Fin (r + 1) → SimplexCategoryᵒᵖ) ⥤ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory C)
    (X Y : C) :
    (coordinateDiagonalAssembly r
      (D ⋙ quasicategoryEnrichedEvaluationFunctor X ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) ▷
        (X ⟶[SSet.{u}] Y)) ≫
      coordinateEnrichedDiagonalAction D (multiIndexDiagonal (r + 1)) X Y =
    (α_ (Δ[1] : SSet.{u})
      (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ oneDirectionIndex r ⋙
        D ⋙ quasicategoryEnrichedEvaluationFunctor X ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget))
      (X ⟶[SSet.{u}] Y)).hom ≫
      ((Δ[1] : SSet.{u}) ◁ coordinateEnrichedDiagonalAction D
        (multiIndexDiagonal r ⋙ oneDirectionIndex r) X Y) ≫
      coordinateDiagonalAssembly r
        (D ⋙ quasicategoryEnrichedEvaluationFunctor Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  change (coordinateEnrichedDiagonalAction D (multiIndexDiagonal (r + 1)) X Y).app n
      (((D.map (oneDirectionAssemblyIndex r n (stdSimplex.objEquiv z.1.1))).val X).app n
        z.1.2, z.2) =
    ((D.map (oneDirectionAssemblyIndex r n (stdSimplex.objEquiv z.1.1))).val Y).app n
      ((coordinateEnrichedDiagonalAction D
        (multiIndexDiagonal r ⋙ oneDirectionIndex r) X Y).app n (z.1.2, z.2))
  have h := congrArg (fun q => q.app n (z.1.2, z.2))
    ((D.map (oneDirectionAssemblyIndex r n (stdSimplex.objEquiv z.1.1))).property X Y)
  exact (coordinateEnrichedDiagonalAction_app D (multiIndexDiagonal (r + 1)) X Y n
    (((D.map (oneDirectionAssemblyIndex r n (stdSimplex.objEquiv z.1.1))).val X).app n
      z.1.2) z.2).trans (h.trans
        (congrArg (fun x =>
          ((D.map (oneDirectionAssemblyIndex r n (stdSimplex.objEquiv z.1.1))).val Y).app n x)
          (coordinateEnrichedDiagonalAction_app D
            (multiIndexDiagonal r ⋙ oneDirectionIndex r) X Y n z.1.2 z.2).symm))

end SerrePositivity.KST.SConstruction
