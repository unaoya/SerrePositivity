module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveHornFaceAgreement
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftStrictTransportWeightedNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Kan 値 weighted nerve の射影の left fibration 性。
方針：最後の係数値で充填した単体を初区間へ追加し、全ての指定面の一致を使って戻す。
規約：元の通常の圏の対象と射の宇宙は u、係数も SSet.{u} に取る。
使われ方：Kerodon §5.3.3（Tag 025W）、strict transport の weighted nerve からの left fibration の復元。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：weighted nerve の相対左ホーンは最後の係数値が Kan なら充填できる。
方針：構成した候補の全ての面の一致を Yoneda の表示で単体集合の射へ戻す。
規約：必要な Kan 性は指定した底の射列の最後の値だけ。
使われ方：Kerodon §5.3.3（Tag 025W）、Kan 値 weighted nerve の左ホーンの持ち上げ。 -/
lemma exists_weightedNerve_leftHorn_lift {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    [KanComplex (F.obj (σ.obj (Fin.last (n + 1))))] (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    ∃ H : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F,
      (horn (n + 1) k).ι ≫ H = a ∧ H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = SSet.yonedaEquiv.symm σ := by
  obtain ⟨ψ, hp, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.exists_weightedNerveHorn_candidate F σ k hk a ha
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1) := ⟨σ, ψ⟩
  let H : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F := SSet.yonedaEquiv.symm s
  have hface (j : Fin (n + 2)) (hj : j ≠ k) : stdSimplex.δ j ≫ H = horn.ι k j hj ≫ a := by
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHorn_candidate_face_agreement F σ k hk a ha ψ hp ht j hj
    calc
      _ = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ j) s) :=
        SSet.yonedaEquiv_symm_naturality_left (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (SimplexCategory.δ j) s
      _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv (horn.ι k j hj ≫ a)) :=
        congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (n := ⦋n⦌)).symm he
      _ = _ := SSet.yonedaEquiv.symm_apply_apply _
  refine ⟨H, horn.hom_ext' hface, ?_⟩
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

/-- 概要：Kan 値の単体集合図式の weighted nerve の射影は left fibration。
方針：相対左ホーンの持ち上げを、指定した底の射列の最後の Kan 値で構成する。
規約：全ての正次元と最後以外の全ての欠ける面を扱う。
使われ方：Kerodon §5.3.3（Tag 025W）、通常の圏上の Kan 値表現からの left fibration の構成。 -/
@[kerodon 036N]
instance weightedNerveProjection_leftFibration {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) where
  mem := by
    intro A B i hi
    cases hi with
    | @intro n k hk =>
      constructor
      intro a b sq
      let σ := SSet.yonedaEquiv b
      have hb : SSet.yonedaEquiv.symm σ = b := SSet.yonedaEquiv.symm_apply_apply _
      have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
          (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ := by
        rw [hb]
        exact sq.w
      obtain ⟨H, hH, hHp⟩ := exists_weightedNerve_leftHorn_lift F σ k (ne_of_lt hk) a ha
      exact CommSq.HasLift.mk' { l := H, fac_left := hH, fac_right := hHp.trans hb }

/-- 概要：left fibration の strict transport の weighted nerve は同じ底上の left fibration。
方針：strict transport の各値の Kan 性を一般の weighted nerve の射影に適用する。
規約：元の全空間との同値は後続の scaffold の比較で示す。
使われ方：Kerodon §§5.3.3（Tag 025W）–5.3.5（Tag 037H）、strict transport 表現からの left fibration の復元候補。 -/
instance leftStrictTransportWeightedProjection_leftFibration
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportWeightedProjection p) := by
  have (c : C) : KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p).obj c) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport_kanComplex p c
  exact weightedNerveProjection_leftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p)

/-- 概要：Kan 値 weighted nerve の全空間は quasicategory。
方針：底の通常の nerve の quasicategory 性と射影の inner fibration 性を使う。
規約：係数の各値に Kan 性を仮定する。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve の全空間を ∞ 圏として比較するための構造。 -/
instance weightedNerve_quasicategory {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) :=
  quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)

/-- 概要：left fibration の strict transport の weighted nerve の全空間は quasicategory。
方針：復元候補の射影の left fibration 性から inner fibration の全空間の判定を使う。
規約：通常の圏 C の nerve を底に取る。
使われ方：Kerodon §§5.3.3（Tag 025W）–5.3.5（Tag 037H）、元の全空間との ∞ 圏の比較の始域。 -/
instance leftStrictTransportWeightedNerve_quasicategory
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportWeightedNerve p) :=
  quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportWeightedProjection p)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
