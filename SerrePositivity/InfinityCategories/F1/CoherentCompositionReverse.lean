module

public import SerrePositivity.InfinityCategories.F1.PointSlicePrismReverse
public import SerrePositivity.InfinityCategories.F1.CoherentPrismEvaluation
public import SerrePositivity.InfinityCategories.F1.FiberTransportFamily

/-!
概要：豊穣合成の右 slice prism を左 coslice の輸送族へ反転する。
方針：パラメーターの反転と因子交換の後で、両端と底の射の式を移す。
規約：係数は第二の豊穣 Hom、底のパラメーターは第一の豊穣 Hom。
使われ方：全パラメーターを持つ coslice の標準輸送と普遍輸送の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：反転した豊穣 Hom を反対 nerve の左 coslice fiber に写す比較。
方針：右 Hom の fiber 比較を反転し、slice の反転 fiber 同型を合成する。
規約：X から Z への射は反対 nerve では Z から X への射となる。
使われ方：反転した合成 prism の始点と終点。 -/
def coherentReverseSliceFiberComparison {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Z : C) :
    ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z)).op ⟶
      vertexFiber (sliceUnderProjection
        (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (coherentNerveVertex Z))))
        (SSet.opObjEquiv.symm (coherentNerveVertex X)) :=
  SSet.opFunctor.map (coherentHomComparison X Z ≫ pinchedHomToSliceFiber _ _) ≫
    (pointSliceReverseFiberIso (coherentNerveVertex Z) (coherentNerveVertex X)).hom

/-- 概要：合成 prism の反転で係数と底パラメーターを適切な順に置き直す射。
方針：反転した二つの直積因子を交換し、直積と反転の同型を合成する。
規約：始域は第二の Hom の反転、第一の Hom の反転の順。
使われ方：FiberTransportFamily の係数を第一因子に合わせる。 -/
def coherentReverseCompositionParameters {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y Z : C) :
    ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)).op ⊗
      ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)).op ⟶
    ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)).op :=
  (β_ _ _).hom ≫ (opTensorIso _ _).hom

/-- 概要：反転した二つの Hom に対する豊穣合成。
方針：係数を先頭に並べた直積を元の反転直積へ移し、合成射を反転して適用する。
規約：時刻一の輸送の終点となる。
使われ方：全パラメーターの輸送の作用を豊穣合成で表示する。 -/
def coherentReverseHomComposition {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y Z : C) :
    ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)).op ⊗
      ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)).op ⟶
    ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z)).op :=
  coherentReverseCompositionParameters X Y Z ≫ SSet.opFunctor.map (coherentHomComposition X Y Z)

/-- 概要：合成の反転 prism の底の辺の族。
方針：第一の豊穣射の既存の区間比較を区間とパラメーターについて反転する。
規約：始点は Y、終点は X を反対 nerve の頂点として表す。
使われ方：輸送族と普遍輸送に共通する底の全パラメーター。 -/
def coherentReverseHomInterval {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    Δ[1] ⊗ ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)).op ⟶
      (SimplicialNerve C).op :=
  reversePrism (intervalMappingUncurry
    (coherentHomComparison X Y ≫ pinchedHomToIntervalMappingSpace _ _))

/-- 概要：豊穣合成の右 slice prism を係数が先頭の左 coslice prism に反転する。
方針：slice の反転の前で係数と底の直積因子を並べ直す。
規約：始点に第二の Hom、終点に二つの Hom の合成を置く。
使われ方：標準の全パラメーター付き coslice 輸送。 -/
def coherentCompositionReversePrism {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y Z : C) :
    Δ[1] ⊗ (((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)).op ⊗
      ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)).op) ⟶
    sliceUnder (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (coherentNerveVertex Z))) :=
  (Δ[1] ◁ coherentReverseCompositionParameters X Y Z) ≫
    reversePointSlicePrism (coherentNerveVertex Z) (coherentCompositionPrism X Y Z)

/-- 概要：反転した合成 prism の始点は第二の射の fiber 比較。
方針：元の一端点の公式を反転し、因子交換後の第二射影を第一射影と同定する。
規約：第一の Hom の全パラメーターは始点では忘れる。
使われ方：FiberTransportFamily の初期条件。 -/
lemma coherentCompositionReversePrism_zero {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y Z : C) :
    prismEndpoint 0 _ ≫ coherentCompositionReversePrism X Y Z =
      fst _ _ ≫ coherentReverseSliceFiberComparison Y Z ≫ vertexFiberι _ _ := by
  dsimp only [coherentCompositionReversePrism]
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc]
  have h := reversePointSlicePrism_endpoint (coherentNerveVertex Z) (coherentNerveVertex Y)
    (coherentCompositionPrism X Y Z) 0
    (snd _ _ ≫ coherentHomComparison Y Z ≫ pinchedHomToSliceFiber _ _)
    (by simpa only [Category.assoc, show (0 : Fin 2).rev = 1 by decide] using
      coherentCompositionPrism_one X Y Z)
  rw [h]
  dsimp only [coherentReverseSliceFiberComparison]
  rw [Category.assoc, pointSliceReverseFiberIso_ι]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：反転した合成 prism の終点は反転した豊穣合成の fiber 比較。
方針：元の零端点を反転し、同じ fiber 同型で終点を移す。
規約：両方の Hom パラメーターを終点でも保持する。
使われ方：FiberTransportFamily の終点条件。 -/
lemma coherentCompositionReversePrism_one {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y Z : C) :
    prismEndpoint 1 _ ≫ coherentCompositionReversePrism X Y Z =
      coherentReverseHomComposition X Y Z ≫
        coherentReverseSliceFiberComparison X Z ≫ vertexFiberι _ _ := by
  dsimp only [coherentCompositionReversePrism]
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc]
  have h := reversePointSlicePrism_endpoint (coherentNerveVertex Z) (coherentNerveVertex X)
    (coherentCompositionPrism X Y Z) 1
    (coherentHomComposition X Y Z ≫ coherentHomComparison X Z ≫ pinchedHomToSliceFiber _ _)
    (by simpa only [Category.assoc, show (1 : Fin 2).rev = 0 by decide] using
      coherentCompositionPrism_zero X Y Z)
  rw [h]
  dsimp only [coherentReverseHomComposition, coherentReverseSliceFiberComparison]
  simp only [SSet.opFunctor.map_comp, Category.assoc]

/-- 概要：反転した合成 prism は第一の射の反転した区間比較を被覆する。
方針：右 slice の射影の式を反転し、直積因子の交換を計算する。
規約：底の射は係数を忘れ、第一の Hom の全パラメーターだけを保つ。
使われ方：FiberTransportFamily の底上の可換性。 -/
lemma coherentCompositionReversePrism_projection {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y Z : C) :
    coherentCompositionReversePrism X Y Z ≫ sliceUnderProjection
      (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (coherentNerveVertex Z))) =
    (Δ[1] ◁ snd _ _) ≫ coherentReverseHomInterval X Y := by
  dsimp only [coherentCompositionReversePrism]
  rw [Category.assoc, reversePointSlicePrism_projection, coherentCompositionPrism_projection,
    reversePrism_precomp]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：反転した豊穣合成は左 coslice の全パラメーター付き輸送族を与える。
方針：構成した prism と二つの端点・射影の厳密な公式を構造体へ束ねる。
規約：局所 Kan 性は輸送族の構成自体には不要。
使われ方：普遍的な fiber transport と豊穣合成の作用の比較。 -/
def coherentCompositionReverseTransportFamily {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y Z : C) :
    FiberTransportFamily (b := SSet.opObjEquiv.symm (coherentNerveVertex X))
      (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (coherentNerveVertex Z))))
      (coherentReverseSliceFiberComparison Y Z) (coherentReverseHomInterval X Y) where
  endpoint := coherentReverseHomComposition X Y Z ≫ coherentReverseSliceFiberComparison X Z
  prism := coherentCompositionReversePrism X Y Z
  start := coherentCompositionReversePrism_zero X Y Z
  finish := coherentCompositionReversePrism_one X Y Z
  over_base := coherentCompositionReversePrism_projection X Y Z

end SerrePositivity.InfinityCategories
