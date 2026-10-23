module

public import SerrePositivity.InfinityCategories.F1.Fibrations.RightFibrationYoneda
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorExtensionEndpoint

/-!
概要：right anodyne な指定領域で一致する、同じ底上の二つの実持ち上げの同型。
方針：実相対関手の制限の自明 Kan 性から、指定頂点同型を充満忠実に戻す。
規約：底の図式と指定制限を厳密に保持。使われ方：補間後の元の全変換の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ right anodyne 領域で一致する元の二つの持ち上げは、相対関手空間で同型。 -/
def rightAnodyneRelativeLiftIso {A T E B : SSet.{u}} (p : E ⟶ B) [RightFibration p]
    (b : A ⟶ B) (i : T ⟶ A) (hi : rightAnodyneExtensions i)
    (f g : A ⟶ E) (hf : f ≫ p = b) (hg : g ≫ p = b) (h : i ≫ f = i ≫ g) :
    VertexIso (relativeFunctorVertex p b f hf) (relativeFunctorVertex p b g hg) := by
  haveI := relativeFunctorPre_trivialKanFibration_of_rightAnodyne p b i hi
  have he := isQCatEquivalence_of_trivialKanFibration (relativeFunctorPre p b i)
  apply he.isFullyFaithful.preimageVertexIso
  apply eqToIso
  apply congrArg SSet.HomotopyCategory.mk
  rw [relativeFunctorPre_vertex, relativeFunctorPre_vertex]
  apply Subtype.ext
  exact congrArg functorVertex h

/-- 相対持ち上げの同型を、元の全図式の同じ関手同型へ写す。 -/
def rightAnodyneLiftFunctorIso {A T E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [RightFibration p] (b : A ⟶ B) (i : T ⟶ A)
    (hi : rightAnodyneExtensions i) (f g : A ⟶ E)
    (hf : f ≫ p = b) (hg : g ≫ p = b) (h : i ≫ f = i ≫ g) : FunctorIso f g := by
  letI : Quasicategory E := quasicategory_of_innerFibration p
  exact VertexIso.map (rightAnodyneRelativeLiftIso p b i hi f g hf hg h)
    (vertexFiberι ((ihom A).map p) (functorVertex b))

end SerrePositivity.InfinityCategories.F2.Ind
