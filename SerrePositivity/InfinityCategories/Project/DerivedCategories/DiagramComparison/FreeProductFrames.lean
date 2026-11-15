module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductDiagramNaturality

/-!
概要：積重みと正規化テンソルを余単体的な複体図式として並べる。
方針：自由正規化鎖への後合成と図式圏のテンソル関手を使う。
規約：余単体の全作用素を持つ元の積・テンソルを使う。
使われ方：HA 1.2.4、G10 の全単体 Hom 比較の始域。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type v) [Category.{w} J]

/-- 自由負次数鎖を各点に作用させる元の図式関手。 -/
def freeNegativeChainsDiagramFunctor :
    (J ⥤ SSet.{u}) ⥤ (J ⥤ CochainComplex (ModuleCat A) ℤ) :=
  (Functor.whiskeringRight J SSet.{u} (CochainComplex (ModuleCat A) ℤ)).obj
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) (ModuleCat A)).obj
      (ModuleCat.free A) ⋙ normalizedMooreComplex (ModuleCat A) ⋙
        ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A))

/-- 元の自然変換への作用との照合。 -/
theorem freeNegativeChainsDiagramFunctor_map {X Y : J ⥤ SSet.{u}} (f : X ⟶ Y) :
    (freeNegativeChainsDiagramFunctor A J).map f = freeNegativeChainsDiagramMap f := rfl

variable {J} (X : J ⥤ SSet.{u}) (P : SimplexCategory ⥤ (J ⥤ SSet.{u}))

/-- 各余単体で積を取り、元の自由正規化鎖へ送る族。 -/
def freeProductFrame : SimplexCategory ⥤ (J ⥤ CochainComplex (ModuleCat A) ℤ) :=
  P ⋙ tensorLeft X ⋙ freeNegativeChainsDiagramFunctor A J

/-- 各余単体で自由正規化鎖を取り、元のテンソルへ送る族。 -/
def freeTensorFrame : SimplexCategory ⥤ (J ⥤ CochainComplex (ModuleCat A) ℤ) :=
  P ⋙ freeNegativeChainsDiagramFunctor A J ⋙
    tensorLeft (freeNegativeChainsDiagram (A := A) X)

variable (φ : simplicialRingCoefficient.{u} →+* A)

/-- 全余単体作用素と可換な指定 AW。 -/
def freeProductFrameAW : freeProductFrame A X P ⟶ freeTensorFrame A X P where
  app n := freeProductDiagramAW φ X (P.obj n)
  naturality n m f := by
    have h := freeProductDiagramAW_naturality φ (𝟙 X) (P.map f)
    have hi : (freeNegativeChainsDiagramFunctor A J).map (𝟙 X) =
        𝟙 (freeNegativeChainsDiagram (A := A) X) :=
      (freeNegativeChainsDiagramFunctor A J).map_id X
    rw [← freeNegativeChainsDiagramFunctor_map, ← freeNegativeChainsDiagramFunctor_map,
      ← freeNegativeChainsDiagramFunctor_map, hi, id_tensorHom, id_tensorHom] at h
    exact h

/-- 全余単体作用素と可換な指定 shuffle。 -/
def freeProductFrameShuffle : freeTensorFrame A X P ⟶ freeProductFrame A X P where
  app n := freeProductDiagramShuffle φ X (P.obj n)
  naturality n m f := by
    have h := freeProductDiagramShuffle_naturality φ (𝟙 X) (P.map f)
    have hi : (freeNegativeChainsDiagramFunctor A J).map (𝟙 X) =
        𝟙 (freeNegativeChainsDiagram (A := A) X) :=
      (freeNegativeChainsDiagramFunctor A J).map_id X
    rw [← freeNegativeChainsDiagramFunctor_map, ← freeNegativeChainsDiagramFunctor_map,
      ← freeNegativeChainsDiagramFunctor_map, hi, id_tensorHom, id_tensorHom] at h
    exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
