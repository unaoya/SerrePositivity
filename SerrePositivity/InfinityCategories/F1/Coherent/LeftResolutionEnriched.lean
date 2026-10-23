module

public import SerrePositivity.InfinityCategories.F1.Coherent.LeftResolution
public import SerrePositivity.InfinityCategories.F1.Coherent.ResolutionEnrichedComparison
public import SerrePositivity.InfinityCategories.F1.KanModels.KanPointHomNaturality

/-!
概要：左 Hom の旗の解像の高次パラメーター付き作用と豊穣自己関手。
方針：右側のパラメーター付き作用を二つの反転で共役し、対象とパラメーターの二重反転を消す。
規約：パラメーターは元の宇宙に保持し、通常の射だけの自然性に制限しない。
使われ方：Kerodon Proposition 4.6.7.16、Corollary 5.6.0.6、左 fiber の模型の高次の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：左 Hom の解像にパラメーター付きの写像を作用させる。
方針：写像を反転して右側の作用を適用し、再び反転してパラメーターの二重反転を戻す。
規約：入力は X⊗T→Y、出力は左解像 X⊗T→左解像 Y。
使われ方：Kerodon Proposition 4.6.7.16、左解像の豊穣 Hom の作用の入力。 -/
noncomputable def coherentLeftResolutionParameterizedMap {X Y T : SSet.{u}} (f : X ⊗ T ⟶ Y) :
    coherentLeftResolution X ⊗ T ⟶ coherentLeftResolution Y :=
  (coherentLeftResolution X ◁ (SSet.opFunctorCompOpFunctorIso.app T).inv) ≫
    (HomotopyLimits.oppositeTensorIso (coherentResolutionRightAdjoint.obj X.op) T.op).inv ≫
      SSet.opFunctor.map (coherentResolutionParameterizedMap
        ((HomotopyLimits.oppositeTensorIso X T).inv ≫ SSet.opFunctor.map f))

/-- 概要：左解像は全ての内部 Hom の単体に作用する。
方針：内部 Hom の評価にパラメーター付き作用を適用して curry する。
規約：X と Y の Kan 性は不要。
使われ方：Kerodon Corollary 5.6.0.6、左 Hom の具体的な模型の豊穣作用。 -/
noncomputable def coherentLeftResolutionEnrichedMap (X Y : SSet.{u}) :
    (ihom X).obj Y ⟶ (ihom (coherentLeftResolution X)).obj (coherentLeftResolution Y) :=
  curry (coherentLeftResolutionParameterizedMap (uncurry (𝟙 ((ihom X).obj Y))))

/-- 概要：左 Hom の解像は Kan 複体の単体的圏の豊穣自己関手。
方針：解像の旗の各単体で単位と合成を計算し、二重反転した値を同じものとして比較する。
規約：高次の Hom の全パラメーターに作用する。
使われ方：Kerodon Corollary 5.6.0.6、左 fiber の模型を一般の coherent な図式へ適用する。 -/
noncomputable def coherentLeftResolutionKanEnriched :
    EnrichedFunctor SSet.{u} KanObject.{u} KanObject.{u} where
  obj X := ⟨coherentLeftResolution X.obj, inferInstance⟩
  map X Y := coherentLeftResolutionEnrichedMap X.obj Y.obj
  map_id X := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, t⟩
    apply SSet.opObjEquiv.injective
    apply ULift.ext
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro s
    apply SSet.opObjEquiv.injective
    rfl
  map_comp X Y Z := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, f, g⟩
    apply SSet.opObjEquiv.injective
    apply ULift.ext
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro s
    apply SSet.opObjEquiv.injective
    rfl

/-- 概要：左解像への標準比較は任意のパラメーター付き写像と可換。
方針：反転した写像に対する右解像の可換式を反転前の値で評価する。
規約：X・Y・T の Kan 性は不要。
使われ方：Kerodon Proposition 4.6.7.16、左 fiber の比較の豊穣自然性。 -/
lemma coherentLeftResolutionParameterizedMap_comparison {X Y T : SSet.{u}} (f : X ⊗ T ⟶ Y) :
    (coherentLeftResolutionComparison X ▷ T) ≫ coherentLeftResolutionParameterizedMap f =
      f ≫ coherentLeftResolutionComparison Y := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  apply SSet.opObjEquiv.injective
  exact congrArg (fun m : X.op ⊗ T.op ⟶ coherentResolutionRightAdjoint.obj Y.op ↦
    m.app n (SSet.opObjEquiv.symm x, SSet.opObjEquiv.symm t))
    (coherentResolutionParameterizedMap_comparison
      ((HomotopyLimits.oppositeTensorIso X T).inv ≫ SSet.opFunctor.map f))

end SerrePositivity.InfinityCategories
