module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanSetCone
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreReverse

/-!
概要：反転した BK 重みから、元の Tot を頂点とする指定錐入力を作る。
方針：Moore 反転の指定鎖射を既存の錐代表に前合成し、実 Dold–Kan Hom 同値を使う。
規約：反転の符号と正規化射影を保持し、元の恒等射からの代表を選び直さない。
使われ方：HA 1.2.4、G10 の反転豊穣 Hom による native 錐比較への入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 単体順序を反転した線形 BK 重みからの、同じ指定錐の複体代表。 -/
def reflectedBousfieldKanConeRepresentative (X : CosimplicialObject (Complex A)) :
    (((normalizedMooreComplex _).obj
      (linearizedSimplicialWeight A (SimplicialObject.opFunctor.obj bousfieldKanSetWeight))).extend
        ComplexShape.embeddingDownNat) ⟶ bousfieldKanConeHomDiagram X :=
  by
    let r := normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight)
    have g : (((normalizedMooreComplex _).obj
        (linearizedSimplicialWeight A bousfieldKanSetWeight)).extend
          ComplexShape.embeddingDownNat) ⟶ bousfieldKanConeHomDiagram X := by
      rw [linearizedBousfieldKanSetWeight]
      exact normalizedBousfieldKanConeRepresentative X
    exact (ComplexShape.embeddingDownNat.extendFunctor
      (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A)).map r ≫ g

/-- 反転重み上の全単体作用素を持つ、同じ Tot の集合的錐入力。 -/
def reflectedBousfieldKanSetCone (X : CosimplicialObject (Complex A)) :
    (SimplicialObject.opFunctor.obj bousfieldKanSetWeight) ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖᵒᵖ (Type 0) (Type u)).obj uliftFunctor.{u,0} ⟶
    ((Abelian.DoldKan.Γ : ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℕ ⥤
      SimplicialObject (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A)).obj
        ((bousfieldKanConeHomDiagram X).truncLE' (ComplexShape.embeddingUpIntLE 0))) ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖᵒᵖ (ModuleCat.{u} A) (Type u)).obj
        (forget (ModuleCat.{u} A)) :=
  normalizedLinearWeightHomEquiv A (SimplicialObject.opFunctor.obj bousfieldKanSetWeight)
    (bousfieldKanConeHomDiagram X) (reflectedBousfieldKanConeRepresentative X)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
