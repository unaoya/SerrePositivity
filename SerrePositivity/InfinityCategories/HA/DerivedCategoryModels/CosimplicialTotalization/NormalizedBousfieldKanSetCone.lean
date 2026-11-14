module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanConeRepresentative
public import SerrePositivity.HomologicalAlgebra.NormalizedLinearWeightHom

/-!
概要：元の Tot の指定 BK 錐代表を、集合的 BK 重みからの単体的自然変換へ移す。
方針：二重反対圏上の同じ over 重みを線形化前に固定し、実正規化 Hom 同値を適用する。
規約：頂点は元の Tot。単体方向と Δ 方向の全作用素を持つ。native 錐への輸送は別工程。
使われ方：HA 1.2.4、G10 の指定 join 錐への集合的な入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 同じ二重反対圏で添字付けた、線形化前の BK over 重み。 -/
def bousfieldKanSetWeight : SimplicialObject (SimplexCategoryᵒᵖᵒᵖ ⥤ Type) :=
  ((opOpEquivalence SimplexCategory).functor ⋙
    SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight
      SimplexCategory).flip

/-- 線形化した集合的重みは、これまで使った係数 over 重みそのもの。 -/
theorem linearizedBousfieldKanSetWeight :
    linearizedSimplicialWeight A bousfieldKanSetWeight =
      doubleOppositeOverWeight SimplexCategory (ModuleCat.of A A) := rfl

/-- 指定錐の係数 Hom 図式を、図式圏の非有界複体として扱う。 -/
def bousfieldKanConeHomDiagram (X : CosimplicialObject (Complex A)) :
    CochainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℤ :=
  (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj
    (doubleOppositeDiagram ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X))

/-- 元の Tot の恒等射から得る、全作用素を持つ集合的 BK 錐の入力。 -/
def normalizedBousfieldKanSetCone (X : CosimplicialObject (Complex A)) :
    bousfieldKanSetWeight ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖᵒᵖ (Type 0) (Type u)).obj uliftFunctor.{u,0} ⟶
    ((Abelian.DoldKan.Γ : ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℕ ⥤
      SimplicialObject (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A)).obj
        ((bousfieldKanConeHomDiagram X).truncLE' (ComplexShape.embeddingUpIntLE 0))) ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖᵒᵖ (ModuleCat.{u} A) (Type u)).obj
        (forget (ModuleCat.{u} A)) :=
  normalizedLinearWeightHomEquiv A bousfieldKanSetWeight (bousfieldKanConeHomDiagram X)
    (normalizedBousfieldKanConeRepresentative X)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
