module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.UnitMappingVertices
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedPrismEvaluation
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEquivalenceLiftingFibration

/-!
概要：実単位の母空間と随伴単位の全部分空間が Kan であることを検証する。
方針：Kan 基底上の left fibration の可逆性反映と、全部分複体の充満忠実性を使う。
規約：モデル構造の instance を仮定せず、全ホーンの持ち上げ性だけを使う。
使われ方：両射影のファイバーの比較と、core の包含による情報の保持。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

instance unitMappingBase_kanComplex (C D : PresentableInfinityObject.{u}) :
    KanComplex (PrLMappingSpace C D ⊗ PrRMappingSpace D C) :=
  prismParameterProduct_kanComplex _ _

/-- 概要：実単位の母空間は Kan 複体。
方針：left fibration による可逆性の反映で全辺を可逆にし、Kan 判定を使う。
規約：単位の随伴性は要求しない。
使われ方：単位条件の全部分複体の Kan 性。 -/
instance rawAdjointUnitSpace_kanComplex (C D : PresentableInfinityObject.{u}) :
    KanComplex (RawAdjointUnitSpace C D) := by
  let p := pullback.snd
    (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
    (unitComposition C D)
  have : IsGroupoid (hoFunctor.obj (RawAdjointUnitSpace C D)) := by
    constructor
    intro x y f
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
    obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective x y f
    exact leftFibration_reflects_invertibleEdge p e
      (IsGroupoid.all_isIso (C := hoFunctor.obj (PrLMappingSpace C D ⊗ PrRMappingSpace D C)) _)
  exact kanComplex_of_isGroupoid _

/-- 概要：実単位の母空間の底射影は全ホーンを持ち上げる。
方針：Kan 複体間の left fibration のホーン判定を適用する。
規約：Fibration は具体的な全ホーンの右持ち上げ性。
使われ方：左右の射影の相対充填の比較。 -/
lemma rawAdjointUnitSpace_projection_fibration (C D : PresentableInfinityObject.{u}) :
    Fibration (pullback.snd
      (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
      (unitComposition C D)) := by
  letI : KanComplex (pullback
      (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
      (unitComposition C D)) := rawAdjointUnitSpace_kanComplex C D
  exact leftFibration_fibration_of_kanComplex _

/-- 概要：随伴単位条件の全部分複体は core を取る前から Kan。
方針：包含の充満忠実性で周囲の辺の可逆性を反映する。
規約：元の単位の高次単体を保持する。
使われ方：core の包含を厳密な同型として比較する。 -/
instance adjointUnitFullSpace_kanComplex (C D : PresentableInfinityObject.{u}) :
    KanComplex (fullSubcomplexOnVertices (RawAdjointUnitSpace C D)
      (fun x ↦ UnitMappingSpaceCondition (unitCorrespondenceHom x)) : SSet.{u + 1}) := by
  let P := fun x : RawAdjointUnitSpace C D _⦋0⦌ ↦
    UnitMappingSpaceCondition (unitCorrespondenceHom x)
  have : IsGroupoid (hoFunctor.obj (fullSubcomplexOnVertices (RawAdjointUnitSpace C D) P)) := by
    constructor
    intro x y f
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
    obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective
      (X := (fullSubcomplexOnVertices (RawAdjointUnitSpace C D) P : SSet.{u + 1})) x y f
    exact IsFullyFaithful.reflects_isInvertibleEdge
      (isFullyFaithful_fullSubcomplexOnVertices_ι (RawAdjointUnitSpace C D) P)
      e (IsGroupoid.all_isIso (C := hoFunctor.obj (RawAdjointUnitSpace C D)) _)
  exact kanComplex_of_isGroupoid _

/-- 概要：随伴単位の空間の core の包含は厳密な同型。
方針：全部分空間の Kan 性に既存の core 同型を適用する。
規約：同型の順方向は元の単体を保持する包含。
使われ方：射影のファイバーを全部分複体の模型で検証する。 -/
def adjointUnitCoreIso (C D : PresentableInfinityObject.{u}) :
    AdjointUnitMappingSpace C D ≅
      (fullSubcomplexOnVertices (RawAdjointUnitSpace C D)
        (fun x ↦ UnitMappingSpaceCondition (unitCorrespondenceHom x)) : SSet.{u + 1}) :=
  quasicategoryCoreIsoOfKan _

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
