module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.RingTheory.Finiteness.Basic

/-!
概要：任意の代数を有限表示代数で近似する模型の圏と cocone。
方針：有限生成代数から元の代数への射の圏で、有限表示な源に制限する。
規約：有限加群性と整性は課さず、同じ宇宙の小さい模型を使う。
使われ方：B03・B04 で元の一般の射を基底を変えずに近似する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- 有限生成代数から全ての可換代数への包含。 -/
abbrev finitePresentationModelFGInclusion : FGAlgCat.{u} R ⥤ CommAlgCat.{u} R :=
  ObjectProperty.ι _

/-- B への有限生成代数の射のうち、始域が有限表示であるという性質。 -/
def finitePresentationModelProperty : ObjectProperty
    (CostructuredArrow (finitePresentationModelFGInclusion R) (CommAlgCat.of R B)) :=
  fun X ↦ Algebra.FinitePresentation R X.left.obj

/-- 有限表示の R-代数から B への射を対象とする模型の圏。 -/
abbrev FinitePresentationModelCategory := (finitePresentationModelProperty R B).FullSubcategory

instance (X : FinitePresentationModelCategory R B) : Algebra.FinitePresentation R X.obj.left.obj :=
  X.property

instance : EssentiallySmall.{u} (FinitePresentationModelCategory R B) :=
  essentiallySmall_of_fully_faithful (finitePresentationModelProperty R B).ι

variable {R B}

/-- 実際の有限表示代数から B への射は、模型の対象を与える。 -/
def finitePresentationModelObj {C : Type u} [CommRing C] [Algebra R C]
    [Algebra.FinitePresentation R C] (g : C →ₐ[R] B) :
    FinitePresentationModelCategory R B := by
  refine ⟨CostructuredArrow.mk (Y := ⟨CommAlgCat.of R C, inferInstance⟩)
    (CommAlgCat.ofHom g), ?_⟩
  change Algebra.FinitePresentation R C
  exact inferInstance

/-- B への写像と可換な準同型は、模型の射を与える。 -/
def finitePresentationModelHomMk {X Y : FinitePresentationModelCategory R B}
    (f : X.obj.left.obj →ₐ[R] Y.obj.left.obj)
    (h : Y.obj.hom.hom.comp f = X.obj.hom.hom) : X ⟶ Y :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (ObjectProperty.homMk (CommAlgCat.ofHom f)) (CommAlgCat.hom_ext h))

variable (R B)

instance : Nonempty (FinitePresentationModelCategory R B) := ⟨finitePresentationModelObj (Algebra.ofId R B)⟩

/-- 模型を実際の可換環へ送る図式。 -/
def finitePresentationModelDiagram : FinitePresentationModelCategory R B ⥤ CommRingCat.{u} :=
  (finitePresentationModelProperty R B).ι ⋙
    CostructuredArrow.proj (finitePresentationModelFGInclusion R) (CommAlgCat.of R B) ⋙
    finitePresentationModelFGInclusion R ⋙ forget₂ (CommAlgCat R) CommRingCat

/-- 各模型の構造射による、元の環 B への実際の cocone。 -/
def finitePresentationModelCocone : Cocone (finitePresentationModelDiagram R B) where
  pt := CommRingCat.of B
  ι.app X := CommRingCat.ofHom X.obj.hom.hom.toRingHom
  ι.naturality {X Y} f := by
    ext x
    have hw : Y.obj.hom.hom.comp f.hom.left.hom.hom = X.obj.hom.hom :=
      congrArg CommAlgCat.Hom.hom f.hom.w
    exact DFunLike.congr_fun hw x

/-- 同じ宇宙の小さい添字。 -/
abbrev FinitePresentationModelIndex := SmallModel.{u} (FinitePresentationModelCategory R B)

/-- 小さい模型から実際の環への図式。 -/
def finitePresentationModelSmallDiagram : FinitePresentationModelIndex R B ⥤ CommRingCat.{u} :=
  (equivSmallModel (FinitePresentationModelCategory R B)).inverse ⋙ finitePresentationModelDiagram R B

/-- 小さい模型に移した B への cocone。 -/
def finitePresentationModelSmallCocone : Cocone (finitePresentationModelSmallDiagram R B) :=
  (finitePresentationModelCocone R B).whisker (equivSmallModel (FinitePresentationModelCategory R B)).inverse

end SerrePositivity.AlgebraicGeometry
