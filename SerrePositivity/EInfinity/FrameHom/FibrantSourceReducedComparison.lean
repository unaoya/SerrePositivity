module

public import SerrePositivity.EInfinity.FrameHom.FibrantFrameSpanNormalization
public import SerrePositivity.InfinityCategories.HomotopyLimits.NerveULiftHom
public import SerrePositivity.InfinityCategories.ModelBridge.ResolutionLeftRoof
public import SerrePositivity.InfinityCategories.ModelBridge.ThreeArrowEquivalence
public import SerrePositivity.InfinityCategories.ModelBridge.ThreeArrowReducedWeakComparison

/-!
概要：fibrant 標的への元の source frame 比較を同じ reduced hammock へ接続する。
方針：全要素圏の宇宙同型、同じ三本矢の包含と正規化を合成する。
規約：元の二列の射と全単体作用素を保持する。
使われ方：bifibrant 部分圏での実 right Kan 比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra Hammock
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X) (Y : C)

/-- 概要：同じ全単体の Hom だけの持ち上げを AsSmall 表示へ送る実同型。
方針：両方を元の nerve の単体の持ち上げと同定する。
規約：同じ全単体を保つ。使われ方：元の比較射への弱同値性の輸送。 -/
def frameElementSmallIso :
    nerve (ULiftHom.{max u v} ((((cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ)) ≅
      nerve (AsSmall.{max u v} ((((cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ)) :=
  NerveULiftHom.iso _ ≪≫ (NerveAsSmall.iso _).symm

/-- 概要：宇宙同型の後の元の三本矢比較は同じ既存の比較射。
方針：全射列で up の後の down を評価する。
規約：実射の等式。使われ方：既存の二列正規化との接続。 -/
lemma frameElementSmallIso_comparison :
    (frameElementSmallIso q Y).hom ≫
      FibrantFrameSpanNormalization.comparisonNerveMap q Y =
        frameElementSpanNerveMap (trivialFibrations C) (trivialCofibrations C)
          q.obj q.augmentation (resolutionAugmentation_trivialFibration q)
          (𝟙 Y) ((trivialCofibrations C).id_mem Y) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  rfl

variable [IsFibrant Y]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

include r in
/-- 概要：元の source frame の同じ三本矢比較射は弱ホモトピー同値。
方針：AsSmall 表示の弱比較を同じ実宇宙同型で前合成する。
規約：標的の fibrancy のみ。使われ方：元の二列比較の弱同値性。 -/
lemma frameElementSpanNerveMap_isWeakHomotopyEquivalence_of_fibrant :
    IsWeakHomotopyEquivalence
      (frameElementSpanNerveMap (trivialFibrations C) (trivialCofibrations C)
        q.obj q.augmentation (resolutionAugmentation_trivialFibration q)
        (𝟙 Y) ((trivialCofibrations C).id_mem Y)) := by
  rw [← frameElementSmallIso_comparison]
  exact (AnodyneWeakDetection.isWeakHomotopyEquivalence (frameElementSmallIso q Y).hom
    (by infer_instance)).comp
      (FibrantFrameSpanNormalization.comparisonNerveMap_isWeakHomotopyEquivalence q Y r)

variable
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

include r cof fib in
/-- 概要：元の二列から reduced hammock への正規化された frame 比較は弱同値。
方針：同じ恒等右脚挿入の照合と三本矢の全比較を合成する。
規約：両関手的分解を明示し、単体集合のモデル構造は使わない。
使われ方：元の frame の全屋根比較の導来不変性。 -/
lemma resolutionLeftRoofNerveMap_normalized_isWeakHomotopyEquivalence_of_fibrant :
    IsWeakHomotopyEquivalence (resolutionLeftRoofNerveMap q Y ≫
      graphNormalization (weakEquivalences C) X Y LeftRoof.word) := by
  rw [resolutionLeftRoofNerveMap_normalization]
  have ht : IsWeakHomotopyEquivalence
      (nerveMap (ThreeArrow.functor (X := X) (Y := Y))) :=
    AnodyneWeakDetection.isWeakHomotopyEquivalence _
      (ThreeArrow.nerveMap_localized_isIso X Y)
  simpa only [Category.assoc] using
    (((frameElementSpanNerveMap_isWeakHomotopyEquivalence_of_fibrant q Y r).comp
    (WeakThreeArrow.inclusion_isWeakHomotopyEquivalence cof fib X Y)).comp ht).comp
      (threeArrowNormalization_isWeakHomotopyEquivalence X Y cof)

end SerrePositivity.EInfinity.FrameHom
