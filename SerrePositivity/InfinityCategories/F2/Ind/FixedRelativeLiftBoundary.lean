module

public import SerrePositivity.InfinityCategories.F1.RightFibrationYoneda
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorExtensionEndpoint
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-!
概要：底の全図式と指定領域への制限を共に固定する、実持ち上げの全空間。
方針：相対前合成の実 fiber を取り、right anodyne 制限では可縮性を使う。
規約：同型の全過程で指定領域を固定。使われ方：区間 D 全体を固定した比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 底と元の指定制限を厳密に固定した持ち上げの実 fiber。 -/
def relativeLiftFixedBoundary {A T E B : SSet.{u}} (p : E ⟶ B) (b : A ⟶ B)
    (i : T ⟶ A) (f : A ⟶ E) (hf : f ≫ p = b) : SSet.{u} :=
  vertexFiber (relativeFunctorPre p b i)
    (relativeFunctorVertex p (i ≫ b) (i ≫ f) (by rw [Category.assoc, hf]))

/-- 元の全底と指定制限を保つ持ち上げを、その同じ fiber の実頂点にする。 -/
def relativeLiftFixedBoundaryVertex {A T E B : SSet.{u}} (p : E ⟶ B) (b : A ⟶ B)
    (i : T ⟶ A) (f : A ⟶ E) (hf : f ≫ p = b) (g : A ⟶ E) (hg : g ≫ p = b)
    (h : i ≫ g = i ≫ f) : (relativeLiftFixedBoundary p b i f hf) _⦋0⦌ :=
  ⟨relativeFunctorVertex p b g hg, by
    rw [pinchedConstant_zero, relativeFunctorPre_vertex]
    apply Subtype.ext
    exact congrArg functorVertex h⟩

/-- right anodyne な指定制限を保つ二つの実持ち上げは、同じ固定制限の fiber 内で同型。 -/
def rightAnodyneFixedRelativeLiftIso {A T E B : SSet.{u}} (p : E ⟶ B) [RightFibration p]
    (b : A ⟶ B) (i : T ⟶ A) (hi : rightAnodyneExtensions i)
    (f : A ⟶ E) (hf : f ≫ p = b) (g : A ⟶ E) (hg : g ≫ p = b) (h : i ≫ g = i ≫ f) :
    VertexIso (relativeLiftFixedBoundaryVertex p b i f hf f hf rfl)
      (relativeLiftFixedBoundaryVertex p b i f hf g hg h) := by
  have := relativeFunctorPre_trivialKanFibration_of_rightAnodyne p b i hi
  have hc := vertexFiber_isContractibleKan (relativeFunctorPre p b i)
    (relativeFunctorVertex p (i ≫ b) (i ≫ f) (by rw [Category.assoc, hf]))
  have : KanComplex (relativeLiftFixedBoundary p b i f hf) := hc.kanComplex
  exact terminalVertexIso (hc.isTerminalVertex _) (hc.isTerminalVertex _)

end SerrePositivity.InfinityCategories.F2.Ind
