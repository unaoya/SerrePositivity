module
public import SerrePositivity.KST.Fibration.VerdierUpperLongHomTransport

/-!
概要：元の実下側読出しから、同じ指定合成端を持つ全 S• 上側族を実構成する。
方針：実長 Hom の座標輸送と Ind-S の指定 native Hom 構成を接続する。
規約：新たな存在入力は不要。全対角の厳密一致と有限端点の指定二胞体回収は別に照合する。
使われ方：K-6 c4 の実上側構成を供給待ちの正規化比較から分離する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：指定上側合成端の入力から、同じ全 S• 二短辺と各点の全 native Hom を持つ族を作る。
方針：同じ入力を元の上側座標へ戻し、Ind-S の実構成へ代入する。
規約：元の全パラメータ・全ホーン・長 Hom を保持する。全対角の等号は主張しない。
使われ方：実下側読出しからの上側二胞体族の構成。 -/
theorem verdierUpperNativeInput_family_exists (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (K : SSet.{u + 1})
    (q : K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierNativeLongHomTarget d))
    (hq : q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
      SSet.const (verdierNativeCompositePoint d 0)) :
    ∃ F : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ F =
        zeroMiddleFullSReconstructionHorn (verdierUpperTriangle d)
          (verdierUpperTriangle_middle_isZero d) K ∧
      ∀ k : K _⦋0⦌,
        HEq ((verdierUpperNativeLongHomTransport d K q).app (Opposite.op ⦋0⦌) k)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamily_exists_of_longHom
    (stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩))
    (fullSRealizationKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 2⟩)) K
    (zeroMiddleFullSFirstFamily (verdierUpperTriangle d) K)
    (zeroMiddleFullSLastFamily (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) K)
    (zeroMiddleFullSReconstructionHorn (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) K)
    (zeroMiddleFullSReconstructionHorn_first _ _ _)
    (zeroMiddleFullSReconstructionHorn_last _ _ _)
  refine (verdierUpperNativeLongHomTransport_full d K q hq).trans ?_
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  rfl

/-- 概要：元の実下側から、直接端を保つ長 Hom 入力と実全 S• 上側族が得られる。
方針：実読出し・実合成端比較・上側座標輸送・同じ全族構成を順に代入する。
規約：(9) 全体の仮定は取らず、全対角の厳密一致や指定有限端点は主張しない。
使われ方：K-6 c4 の残る正規化対角と有限端点照合への実入力。 -/
theorem verdierLowerReadout_upperFamily_exists (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})
    ∃ (L : (Δ[1] : SSet.{u + 1}) ⟶
        (ihom Pu).obj (verdierLowerNativeLongHomTarget d))
      (U : (Δ[1] : SSet.{u + 1}) ⟶ (ihom Pu).obj (verdierNativeLongHomTarget d))
      (F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}),
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        verdierLowerReconstructionCompositeFamily d Δ[1] ∧
      U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        SSet.const (verdierNativeCompositePoint d 0) ∧
      verdierNativeLongHomStart d Δ[1] U =
        verdierNativeLongHomStart d Δ[1] (verdierLowerNativeLongHomTransport d Δ[1] L) ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ F =
        zeroMiddleFullSReconstructionHorn (verdierUpperTriangle d)
          (verdierUpperTriangle_middle_isZero d) Δ[1] ∧
      ∀ k : (Δ[1] : SSet.{u + 1}) _⦋0⦌,
        HEq ((verdierUpperNativeLongHomTransport d Δ[1] U).app (Opposite.op ⦋0⦌) k)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  obtain ⟨L, U, hL, hU, hstart⟩ := verdierLowerNativeReadout_upperInput_exists d
  obtain ⟨F, hF, hnative⟩ := verdierUpperNativeInput_family_exists d Δ[1] U hU
  exact ⟨L, U, F, hL, hU, hstart, hF, hnative⟩

end SerrePositivity.KST.Fibration
