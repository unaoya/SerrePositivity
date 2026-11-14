module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanConeRepresentative
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightEndHomTargetNaturality

/-!
概要：指定BK正規化比較を、係数図式の全射に自然な同じ変換へまとめる。
方針：既存over比較、Moore包含の自然性、指定end–Hom同型の係数自然性を合成。
規約：IS-W2 D01の既存構成の自然性・合成則。指定射を取り換えない。
使われ方：HA 1.2.4、元のTot錐の全パラメータ族の組み立て。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 指定正規化BK Homを全係数図式の全関手にする。 -/
def normalizedBousfieldKanHomFunctor : CosimplicialObject (Complex A) ⥤ Complex A :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖᵒᵖ SimplexCategory (Complex A)).obj
      (opOpEquivalence SimplexCategory).functor ⋙
    functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ) ⋙
    SerrePositivity.EInfinity.PowerOperation.linearHomComplexFunctor A
      (normalizedBousfieldKanWeight.extend ComplexShape.embeddingDownNat)

/-- 同じ指定正規化比較は、元の全図式射に自然。 -/
theorem normalizedBousfieldKanHomComparison_naturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    normalizedBousfieldKanHomComparison X ≫ normalizedBousfieldKanHomFunctor.map f =
      (productTotalFunctor A).map f ≫ normalizedBousfieldKanHomComparison Y := by
  let g := Functor.whiskerLeft (opOpEquivalence SimplexCategory).functor f
  let W := doubleOppositeOverWeight SimplexCategory (ModuleCat.of A A)
  have h₁ := weightEndHomIso_target_naturality_postcompose A
    normalizedBousfieldKanWeight g
  have h₂ := linearWeightEndNormalizationMap_naturality A g W
  have h₃ := bousfieldKanWeightEndTotalComparison.naturality f
  unfold normalizedBousfieldKanHomComparison
  simp only [Category.assoc]
  erw [← h₁]
  rw [← Category.assoc (linearWeightEndNormalizationMap A (doubleOppositeDiagram X) W)]
  erw [h₂]
  rw [Category.assoc]
  rw [← Category.assoc (bousfieldKanWeightEndTotalComparison.app X)]
  erw [← h₃]
  simp only [Category.assoc]
  rfl

/-- 対象ごとの指定射を変えず、全図式射への自然変換へ組み立てる。 -/
def normalizedBousfieldKanHomComparisonNatTrans :
    productTotalFunctor A ⟶ normalizedBousfieldKanHomFunctor where
  app X := normalizedBousfieldKanHomComparison X
  naturality _ _ f := (normalizedBousfieldKanHomComparison_naturality f).symm

/-- 同じHom–Tot比較と指定正規化比較を全図式上で合成する。 -/
def homToNormalizedBousfieldKanNatTrans (P : Complex A) :
    productTotalFunctor A ⋙ homFunctor P ⟶
      homDiagramFunctor P ⋙ normalizedBousfieldKanHomFunctor :=
  (homTotalNatIso P).hom ≫
    Functor.whiskerLeft (homDiagramFunctor P) normalizedBousfieldKanHomComparisonNatTrans

/-- 全自然変換の各成分は、元の指定BK錐代表を作った比較そのもの。 -/
theorem homToNormalizedBousfieldKanNatTrans_app (P : Complex A)
    (X : CosimplicialObject (Complex A)) :
    (homToNormalizedBousfieldKanNatTrans P).app X = homToNormalizedBousfieldKan P X := rfl

/-- 元のBK錐代表の比較は、同じTot射のHom像に自然。 -/
theorem homToNormalizedBousfieldKan_naturality (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (homFunctor P).map ((productTotalFunctor A).map f) ≫ homToNormalizedBousfieldKan P Y =
      homToNormalizedBousfieldKan P X ≫
        normalizedBousfieldKanHomFunctor.map ((homDiagramFunctor P).map f) :=
  (homToNormalizedBousfieldKanNatTrans P).naturality f

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
