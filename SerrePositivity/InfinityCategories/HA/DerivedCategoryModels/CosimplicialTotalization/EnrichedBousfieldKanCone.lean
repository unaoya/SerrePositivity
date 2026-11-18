module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedPointwiseBousfieldKanCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDoldKanHomDiagram

/-!
概要：元の Tot を頂点とする指定 BK 錐入力を、実際の反転豊穣 Hom 図式へ移す。
方針：指定 Γ 同型の全射自然性を使い、既存の豊穣 Hom 関手の図式へ後合成する。
規約：同じ閉射と全高次単体を使う。native 錐の極限性は後続で示す。
使われ方：HA 1.2.4、G10 の BK 比較から native 錐への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 元の余単体図式を、同じ閉複体射の図式として扱う。 -/
def bousfieldKanClosedDiagram (X : CosimplicialObject (Complex A)) :
    SimplexCategoryᵒᵖᵒᵖ ⥤ ClosedCategory A (Complex A) :=
  doubleOppositeDiagram X ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A

/-- 同じ Tot から元の図式への実豊穣 Hom の全図式。 -/
def bousfieldKanEnrichedHomSpaces (X : CosimplicialObject (Complex A)) :
    SimplexCategoryᵒᵖᵒᵖ ⥤ SSet.{u} :=
  bousfieldKanClosedDiagram X ⋙
    (SimplicialCategory.sHomFunctor (ClosedCategory A (Complex A))).obj
      (op (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)))

/-- 実豊穣 Hom と点ごとの Γ Hom の指定同型は全図式射に自然。 -/
def bousfieldKanEnrichedHomIso (X : CosimplicialObject (Complex A)) :
    bousfieldKanEnrichedHomSpaces X ≅ pointwiseBousfieldKanHomSpaces X :=
  Functor.isoWhiskerLeft (doubleOppositeDiagram X)
    (complexDoldKanHomIso A ((productTotalFunctor A).obj X))

/-- 元の BK 重みから実際の反転豊穣 Hom 図式への指定自然変換。 -/
def enrichedBousfieldKanCone (X : CosimplicialObject (Complex A)) :
    (bousfieldKanSetWeight ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖᵒᵖ (Type 0) (Type u)).obj
        uliftFunctor.{u,0}).flip ⟶
      bousfieldKanEnrichedHomSpaces X ⋙ SimplicialObject.opFunctor :=
  reflectedPointwiseBousfieldKanCone X ≫
    Functor.whiskerRight (bousfieldKanEnrichedHomIso X).inv SimplicialObject.opFunctor

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
