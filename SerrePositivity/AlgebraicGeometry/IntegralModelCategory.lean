module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.Basic

/-!
概要：整射の近似に使う、有限・有限表示代数の模型の圏と実際の環の cocone。
方針：有限生成代数の B への costructured arrow の充満部分圏を、小さい模型へ移す。
規約：添字は元の環と同じ宇宙。filtered 性と余極限性は別に証明する。
使われ方：C01 の整拡大を有限・有限表示の段で近似する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- 有限生成代数から全ての可換代数への包含。 -/
abbrev integralModelFGInclusion : FGAlgCat.{u} R ⥤ CommAlgCat.{u} R :=
  ObjectProperty.ι _

/-- B への有限生成代数の射のうち、始域が有限かつ有限表示であるという性質。 -/
def integralModelProperty : ObjectProperty
    (CostructuredArrow (integralModelFGInclusion R) (CommAlgCat.of R B)) :=
  fun X ↦ Module.Finite R X.left.obj ∧ Algebra.FinitePresentation R X.left.obj

/-- 有限・有限表示の R-代数から B への射を対象とする模型の圏。 -/
abbrev IntegralModelCategory := (integralModelProperty R B).FullSubcategory

instance (X : IntegralModelCategory R B) : Module.Finite R X.obj.left.obj := X.property.1
instance (X : IntegralModelCategory R B) : Algebra.FinitePresentation R X.obj.left.obj :=
  X.property.2

instance : EssentiallySmall.{u} (IntegralModelCategory R B) :=
  essentiallySmall_of_fully_faithful (integralModelProperty R B).ι

variable {R B}

/-- 実際の有限・有限表示代数から B への射は、模型の対象を与える。 -/
def integralModelObj {C : Type u} [CommRing C] [Algebra R C]
    [Module.Finite R C] [Algebra.FinitePresentation R C] (g : C →ₐ[R] B) :
    IntegralModelCategory R B := by
  refine ⟨CostructuredArrow.mk (Y := ⟨CommAlgCat.of R C, inferInstance⟩)
    (CommAlgCat.ofHom g), ?_⟩
  change Module.Finite R C ∧ Algebra.FinitePresentation R C
  exact ⟨inferInstance, inferInstance⟩

/-- B への写像と可換な準同型は、模型の射を与える。 -/
def integralModelHomMk {X Y : IntegralModelCategory R B}
    (f : X.obj.left.obj →ₐ[R] Y.obj.left.obj)
    (h : Y.obj.hom.hom.comp f = X.obj.hom.hom) : X ⟶ Y :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (ObjectProperty.homMk (CommAlgCat.ofHom f)) (CommAlgCat.hom_ext h))

variable (R B)

instance : Nonempty (IntegralModelCategory R B) := ⟨integralModelObj (Algebra.ofId R B)⟩

/-- 模型を実際の可換環へ送る図式。 -/
def integralModelDiagram : IntegralModelCategory R B ⥤ CommRingCat.{u} :=
  (integralModelProperty R B).ι ⋙
    CostructuredArrow.proj (integralModelFGInclusion R) (CommAlgCat.of R B) ⋙
    integralModelFGInclusion R ⋙ forget₂ (CommAlgCat R) CommRingCat

/-- 各模型の構造射による、元の環 B への実際の cocone。 -/
def integralModelCocone : Cocone (integralModelDiagram R B) where
  pt := CommRingCat.of B
  ι.app X := CommRingCat.ofHom X.obj.hom.hom.toRingHom
  ι.naturality {X Y} f := by
    ext x
    have hw : Y.obj.hom.hom.comp f.hom.left.hom.hom = X.obj.hom.hom :=
      congrArg CommAlgCat.Hom.hom f.hom.w
    exact DFunLike.congr_fun hw x

/-- 同じ宇宙の小さい添字。 -/
abbrev IntegralModelIndex := SmallModel.{u} (IntegralModelCategory R B)

/-- 小さい模型から実際の環への図式。 -/
def integralModelSmallDiagram : IntegralModelIndex R B ⥤ CommRingCat.{u} :=
  (equivSmallModel (IntegralModelCategory R B)).inverse ⋙ integralModelDiagram R B

/-- 小さい模型に移した B への cocone。 -/
def integralModelSmallCocone : Cocone (integralModelSmallDiagram R B) :=
  (integralModelCocone R B).whisker (equivSmallModel (IntegralModelCategory R B)).inverse

end SerrePositivity.AlgebraicGeometry
