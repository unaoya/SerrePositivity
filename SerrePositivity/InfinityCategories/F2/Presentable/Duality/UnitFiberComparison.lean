module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUniversalUnits
public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.UnitMappingFibers
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceCommaEquivalence

/-!
概要：実単位の対応の右ファイバーを、全関手圏の coslice の底変換へ比較する。
方針：固定した右関手との合成を後合成に同定し、元の単位の族を保持する。
規約：比較は全単体上の射として構成する。
使われ方：普遍単位の可縮な空間との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：右因子を固定した内部 Hom の合成は、元の関手による後合成。
方針：内部 Hom の全単体の成分で固定関手の作用を計算する。
規約：充填性や随伴性は仮定しない。
使われ方：右ファイバーの単位の終域の同定。 -/
lemma internalHomComposition_fixedRight {A B Z : SSet.{u}} (R : B ⟶ Z) :
    CartesianMonoidalCategory.lift (𝟙 ((ihom A).obj B)) (SSet.const (functorVertex R)) ≫
      MonoidalClosed.comp A B Z = (ihom A).map R := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro a
  change R.app d (f.app d (α ≫ 𝟙 d) a) = R.app d (f.app d α a)
  rw [Category.comp_id]

/-- 概要：元の写像空間の右頂点を固定すると合成はその右関手による後合成。
方針：包含と定値写像の積を計算し、内部 Hom の固定右因子の公式を使う。
規約：元の e1 の core の全単体に対する等式。
使われ方：実単位の右ファイバーから全関手圏の coslice への比較。 -/
lemma unitComposition_fixedRight (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    CartesianMonoidalCategory.lift (𝟙 (PrLMappingSpace C D)) (SSet.const w) ≫
      unitComposition C D = leftMappingInclusion C D ≫
        (ihom C.obj).map (rightVertexFunctor w.val) := by
  have hw : (rightMappingInclusion D C).app (Opposite.op ⦋0⦌) w =
      functorVertex (rightVertexFunctor w.val) :=
    ((functorVertexEquiv D.obj C.obj).apply_symm_apply w.val.val).symm
  rw [unitComposition, ← Category.assoc, lift_map, Category.id_comp, SSet.const_comp, hw]
  calc
    _ = (leftMappingInclusion C D ≫ CartesianMonoidalCategory.lift
        (𝟙 ((ihom C.obj).obj D.obj))
        (SSet.const (functorVertex (rightVertexFunctor w.val)))) ≫
          MonoidalClosed.comp C.obj D.obj C.obj := by
      rw [comp_lift, Category.comp_id, SSet.comp_const]
    _ = _ := by rw [Category.assoc, internalHomComposition_fixedRight]

/-- 概要：右関手を固定した実単位の全関手圏上の母空間。
方針：恒等関手の coslice を右関手による後合成に沿って引き戻す。
規約：左関手の保存条件や単位の普遍性はまだ課さない。
使われ方：元の実単位の射影ファイバーを比較する coslice 模型。 -/
def RightUnitCoslice (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : SSet.{u + 1} :=
  pullback (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
    ((ihom C.obj).map (rightVertexFunctor w))

instance rightUnitCoslice_quasicategory (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : Quasicategory (RightUnitCoslice C D w) := by
  let p := pullback.snd
    (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
    ((ihom C.obj).map (rightVertexFunctor w))
  have : LeftFibration p :=
    ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p :=
      sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj)))))⟩
  exact quasicategory_of_innerFibration p

/-- 概要：固定右関手の coslice と comma の標準比較。
方針：元の join 型の単位の族を区間型の族に制限する。
規約：左関手への射影を保持する元の単体集合の射。
使われ方：随伴単位の始対象性を coslice 模型へ移す。 -/
def rightUnitCosliceComparison (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : RightUnitCoslice C D w ⟶ RightUnitComma C D w :=
  HomotopyLimits.cosliceCommaComparison _ _

/-- 概要：固定右関手の coslice の標準比較は全 QCat 同値。
方針：既存の coslice–comma 比較の全空間の同値性を適用する。
規約：頂点の同型だけで代用しない。
使われ方：普遍単位の始対象性と高次の可縮性の移送。 -/
lemma rightUnitCosliceComparison_isQCatEquivalence (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : IsQCatEquivalence (rightUnitCosliceComparison C D w) :=
  HomotopyLimits.cosliceCommaComparison_isQCatEquivalence _ _

/-- 概要：固定右関手の実単位の coslice には始対象が存在する。
方針：comma の始対象を標準比較の逆同値で移す。
規約：元の coslice 模型の全境界の充填による始対象性。
使われ方：実単位の普遍な選択の可縮性。 -/
lemma rightUnitCoslice_hasInitial (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) :
    ∃ x : RightUnitCoslice C D w _⦋0⦌, IsInitialVertex x := by
  obtain ⟨x, hx⟩ := rightUnitComma_hasInitial C D w
  let e := (rightUnitCosliceComparison_isQCatEquivalence C D w).choose
  exact ⟨e.inv.app (Opposite.op ⦋0⦌) x, (e.symm.isInitialVertex_iff x).mp hx⟩

/-- 概要：右射影の固定ファイバーの底は、左射影と固定した右頂点の対。
方針：直積の両射影を計算し、右成分にはファイバーの定値条件を使う。
規約：全単体上の射の厳密な等式。
使われ方：元の実単位を固定右関手の coslice へ送る。 -/
lemma adjointUnitRightFiber_base (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    vertexFiberι (adjointUnitRight C D) w ≫ adjointUnitUnderlying C D ≫
      pullback.snd _ (unitComposition C D) =
    (vertexFiberι (adjointUnitRight C D) w ≫ adjointUnitLeft C D) ≫
      CartesianMonoidalCategory.lift (𝟙 (PrLMappingSpace C D)) (SSet.const w) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, Category.comp_id]
    rfl
  · simp only [Category.assoc, lift_snd, SSet.comp_const]
    exact vertexFiberι_comp (adjointUnitRight C D) w

/-- 概要：実単位の右ファイバーから、全関手圏の固定右 coslice への比較。
方針：元の coslice の成分と左関手の成分を引き戻しに持ち上げる。
規約：元の単位の高次単体を選び直さず保持する。
使われ方：普遍単位の始対象空間とのファイバーの比較。 -/
def adjointUnitRightFiberToCoslice (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    vertexFiber (adjointUnitRight C D) w ⟶ RightUnitCoslice C D w.val :=
  pullback.lift
    (vertexFiberι (adjointUnitRight C D) w ≫ adjointUnitUnderlying C D ≫
      pullback.fst _ (unitComposition C D))
    (vertexFiberι (adjointUnitRight C D) w ≫ adjointUnitLeft C D ≫ leftMappingInclusion C D)
    (by
      rw [Category.assoc, Category.assoc, pullback.condition]
      simpa only [Category.assoc, unitComposition_fixedRight] using
        congrArg (· ≫ unitComposition C D) (adjointUnitRightFiber_base C D w))

/-- 概要：右ファイバーの比較は元の実単位の coslice 成分を保持する。
方針：引き戻しの持ち上げの第一射影を計算する。
規約：全次数での厳密な射の等式。
使われ方：比較の単位の Hom 類を同定する。 -/
lemma adjointUnitRightFiberToCoslice_unit (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    adjointUnitRightFiberToCoslice C D w ≫ pullback.fst _
      ((ihom C.obj).map (rightVertexFunctor w.val)) =
    vertexFiberι (adjointUnitRight C D) w ≫ adjointUnitUnderlying C D ≫
      pullback.fst _ (unitComposition C D) :=
  pullback.lift_fst _ _ _

/-- 概要：右ファイバーの比較は元の左関手の全単体を保持する。
方針：引き戻しの持ち上げの第二射影を計算する。
規約：元の全関手圏への包含を通して比較する。
使われ方：普遍単位の左関手の保存条件を照合する。 -/
lemma adjointUnitRightFiberToCoslice_left (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    adjointUnitRightFiberToCoslice C D w ≫ pullback.snd _
      ((ihom C.obj).map (rightVertexFunctor w.val)) =
    vertexFiberι (adjointUnitRight C D) w ≫ adjointUnitLeft C D ≫ leftMappingInclusion C D :=
  pullback.lift_snd _ _ _

/-- 概要：右ファイバーの coslice 比較は最大 Kan 部分複体へ因子化する。
方針：ファイバーの Kan 性と core の厳密同型を通して core 上の写像を使う。
規約：単位の高次単体を失う離散化は行わない。
使われ方：始対象の全部分空間との比較。 -/
def adjointUnitRightFiberToCore (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    vertexFiber (adjointUnitRight C D) w ⟶
      (quasicategoryCore (RightUnitCoslice C D w.val) : SSet.{u + 1}) :=
  (quasicategoryCoreIsoOfKan _).inv ≫ quasicategoryCoreMap (adjointUnitRightFiberToCoslice C D w)

/-- 概要：core への因子化を元へ含めると同じ coslice 比較。
方針：core 上の写像と包含の自然性、core の同型の逆則を使う。
規約：元の実単位の比較射を変更しない。
使われ方：core 内での検証を元の coslice の計算へ戻す。 -/
lemma adjointUnitRightFiberToCore_ι (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    adjointUnitRightFiberToCore C D w ≫ (quasicategoryCore (RightUnitCoslice C D w.val)).ι =
      adjointUnitRightFiberToCoslice C D w := by
  unfold adjointUnitRightFiberToCore
  rw [Category.assoc, quasicategoryCoreMap_ι, ← Category.assoc]
  change ((quasicategoryCoreIsoOfKan _).inv ≫ (quasicategoryCoreIsoOfKan _).hom) ≫ _ = _
  rw [Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
