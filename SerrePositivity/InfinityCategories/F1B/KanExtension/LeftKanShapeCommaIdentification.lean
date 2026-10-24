module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LocalShapeOppositeHomotopy
public import SerrePositivity.InfinityCategories.F1B.KanExtension.CommaLocalColimits
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaUnitComponent

/-!
概要：反転から作った局所比較と標準余錐から直接作った局所比較は厳密に一致する。
方針：反転前の comma の標的と指定変換を比較し、反転と fiber の包含で戻す。
規約：比較の等式には quasicategory 性を使わない。
使われ方：標準の局所 Kan 余錐へ比較の同値性を適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：反転前の局所比較は元の標準変換を反転して comma に持ち上げた射。
方針：comma の矢印の族と標的の外延性を使う。
規約：指定変換の端点の証明の一致は不要。
使われ方：反転した比較の定義を元の slice の余錐からの比較へ戻す。 -/
lemma kanLeftKanShapeOpIso_comma {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (kanLeftKanShapeOpIso δ c).hom ≫
      kanRightKanShapeToUnitCommaFiber (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c) ≫
        vertexFiberι (unitCommaSource (SSet.opFunctor.map δ)) (SSet.opObjEquiv.symm c) =
      unitCommaLift (SSet.opFunctor.map δ) (SSet.opFunctor.map (SSet.const c))
        (SSet.opFunctor.map (leftKanProjection δ c))
        (kanLeftCommaLiftOppositeHomotopy δ (leftKanProjection δ c) (SSet.const c)
          (kanLeftKanShapeHomotopy δ c)) := by
  apply unitComma_hom_ext
  · apply (cancel_epi (β_ (leftKanShape δ c).op (Δ[1] : SSet.{u})).hom).1
    change (unitCommaHomotopy (_ ≫ _)).h = (unitCommaHomotopy _).h
    rw [unitCommaHomotopy_precomp, unitCommaLift_homotopy_h]
    change ((kanLeftKanShapeOpIso δ c).hom ▷ (Δ[1] : SSet.{u})) ≫
      (unitCommaFiberHomotopy
        (unitCommaFiberCurry (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c)
          (rightKanProjection (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c))
          (kanRightKanShapeHomotopy (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c)))).h = _
    rw [unitCommaFiberCurry_homotopy]
    exact kanLeftKanShapeOpIso_homotopy δ c
  · rw [unitCommaLift_target]
    change (kanLeftKanShapeOpIso δ c).hom ≫
      kanRightKanShapeToUnitCommaFiber (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c) ≫
        SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c) = _
    rw [kanRightKanShapeToUnitCommaFiber_projection, kanLeftKanShapeOpIso_projection]

/-- 概要：comma の fiber の反転同型は全空間への包含を反転する。
方針：fiber の反転と底の同型の後合成は、どちらも包含の値を保つ。
規約：底への等式の証明は証明無関係性で消える。
使われ方：二つの局所比較を全空間で照合する。 -/
lemma kanLeftCommaFiberIso_ι {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (kanLeftCommaFiberIso δ c).hom ≫ vertexFiberι (kanLeftCommaProjection δ) c =
      SSet.opFunctor.map
        (vertexFiberι (unitCommaSource (SSet.opFunctor.map δ)) (SSet.opObjEquiv.symm c)) := rfl

/-- 概要：反転を通した局所比較は標準余錐から直接作った比較に等しい。
方針：fiber の包含を消去し、反転前の comma の比較の等式を使う。
規約：射の厳密な一致。
使われ方：標準の局所余錐に単射な前合成同値の性質を渡す。 -/
lemma kanLeftKanShapeToCommaFiberViaOpposite_eq {K C : SSet.{u}}
    (δ : K ⟶ C) (c : C _⦋0⦌) :
    kanLeftKanShapeToCommaFiberViaOpposite δ c = kanLeftKanShapeToCommaFiber δ c := by
  apply vertexFiber_hom_ext (kanLeftCommaProjection δ) c
  unfold kanLeftKanShapeToCommaFiberViaOpposite
  rw [Category.assoc, Category.assoc, Category.assoc, kanLeftCommaFiberIso_ι]
  change (SSet.opFunctorCompOpFunctorIso.app (leftKanShape δ c)).inv ≫ SSet.opFunctor.map
    ((kanLeftKanShapeOpIso δ c).hom ≫
      kanRightKanShapeToUnitCommaFiber (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c) ≫
        vertexFiberι (unitCommaSource (SSet.opFunctor.map δ)) (SSet.opObjEquiv.symm c)) = _
  rw [kanLeftKanShapeOpIso_comma]
  rw [kanLeftKanShapeToCommaFiber, vertexFiberLift_ι]
  rfl

/-- 概要：標準余錐から作る局所比較は前合成同値。
方針：反転による比較との等式を使う。
規約：δ 自身の fibration 性は不要。
使われ方：標準の局所 Kan 余錐の余極限性を反映する。 -/
lemma kanLeftKanShapeToCommaFiber_isPrecompositionEquivalence {K C : SSet.{u}}
    [Quasicategory K] [Quasicategory C] (δ : K ⟶ C) (c : C _⦋0⦌) :
    IsPrecompositionEquivalence (kanLeftKanShapeToCommaFiber δ c) := by
  rw [← kanLeftKanShapeToCommaFiberViaOpposite_eq]
  exact kanLeftKanShapeToCommaFiberViaOpposite_isPrecompositionEquivalence δ c

/-- 概要：標準余錐から作る局所比較も単射。
方針：反転による比較の単射性を厳密な一致で移す。
規約：充填性は不要。
使われ方：普遍余錐を局所添字へ制限する。 -/
instance kanLeftKanShapeToCommaFiber_mono {K C : SSet.{u}}
    (δ : K ⟶ C) (c : C _⦋0⦌) : Mono (kanLeftKanShapeToCommaFiber δ c) := by
  rw [← kanLeftKanShapeToCommaFiberViaOpposite_eq]
  infer_instance

end SerrePositivity.InfinityCategories.F1B
