module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ConeTipNormalization

/-!
概要：元の小さい一点下添字を、同じ持ち上げた点の下の添字へ厳密に移す。
方針：既存の全 coslice 宇宙同型と標準零単体の形状同型を合成する。
規約：元の点と元の全射影を保持する。
使われ方：元の表示の同じ一段から始まる入力付き filtered 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
open HomotopyLimits

/-- 概要：元の一点の下の全添字の持ち上げは、持ち上げた同じ点の下の全添字と同型。
方針：全 coslice 宇宙同型の後で標準零単体の宇宙同型に沿って制限する。
規約：元の点を変更しない。
使われ方：元の表示段の全 source coslice の正規化。 -/
def pointCosliceUniverseIso {X : SSet.{u}} (x : X _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (sliceUnder (SSet.yonedaEquiv.symm x)) ≅
      sliceUnder ((SSet.yonedaEquiv (X := (SSet.uliftFunctor.{v, u}).obj X)).symm (ULift.up x)) :=
  uliftSliceUnderIso (SSet.yonedaEquiv.symm x) ≪≫
    cosliceShapeIso (uliftStdSimplexIso.{u, v} 0).symm
      ((SSet.uliftFunctor.{v, u}).map (SSet.yonedaEquiv.symm x)) ≪≫
    eqToIso (congrArg sliceUnder (uliftYonedaMap.{u, v} x))

/-- 概要：一点下添字の宇宙同型は、元の全終点射影を保つ。
方針：標準単体の制限と等号輸送の射影を相殺する。
規約：全単体上での厳密な等式。
使われ方：同じ表示の cofinal 性と各 compact 成分の回収。 -/
lemma pointCosliceUniverseIso_projection {X : SSet.{u}} (x : X _⦋0⦌) :
    (pointCosliceUniverseIso.{u, v} x).hom ≫
      sliceUnderProjection
        ((SSet.yonedaEquiv (X := (SSet.uliftFunctor.{v, u}).obj X)).symm (ULift.up x)) =
      (SSet.uliftFunctor.{v, u}).map (sliceUnderProjection (SSet.yonedaEquiv.symm x)) := by
  have hep {A C : SSet.{max u v}} {f g : A ⟶ C} (h : f = g) :
      (eqToIso (congrArg sliceUnder h)).hom ≫ sliceUnderProjection g =
        sliceUnderProjection f := by
    subst g
    rfl
  simp only [pointCosliceUniverseIso, Iso.trans_hom, Category.assoc]
  rw [hep (uliftYonedaMap.{u, v} x)]
  have hshape : (cosliceShapeIso (uliftStdSimplexIso.{u, v} 0).symm
      ((SSet.uliftFunctor.{v, u}).map (SSet.yonedaEquiv.symm x))).hom ≫
      sliceUnderProjection ((uliftStdSimplexIso.{u, v} 0).inv ≫
        (SSet.uliftFunctor.{v, u}).map (SSet.yonedaEquiv.symm x)) =
      sliceUnderProjection ((SSet.uliftFunctor.{v, u}).map (SSet.yonedaEquiv.symm x)) :=
    cosliceShapeIso_projection _ _
  rw [hshape, uliftSliceUnderIso_projection]

/-- 概要：小さい filtered 表示の同じ元の一点の下からの終点射影は right cofinal。
方針：小さい一点前置 coslice の共終性を同じ宇宙持ち上げへ移す。
規約：元の同じ全一点下添字を使う。
使われ方：入力付き表示の元の余極限性。 -/
lemma pointCosliceUniverseProjection_isRightCofinal
    {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I] (i : I _⦋0⦌) :
    IsRightCofinal ((pointCosliceUniverseIso.{u, u + 1} i).hom ≫
      sliceUnderProjection
        ((SSet.yonedaEquiv (X := (SSet.uliftFunctor.{u + 1, u}).obj I)).symm (ULift.up i))) := by
  rw [pointCosliceUniverseIso_projection]
  exact Ind.isRightCofinal_ulift _ (smallPrefix_cosliceProjection_isRightCofinal hμ
    (isKappaSmall_of_finite hμ.aleph0_le _) (SSet.yonedaEquiv.symm i))

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
