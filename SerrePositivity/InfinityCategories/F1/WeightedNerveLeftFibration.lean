module

public import SerrePositivity.InfinityCategories.F1.WeightedNerveHornFaceAgreement
public import SerrePositivity.InfinityCategories.F1.LeftStrictTransportWeightedNerve
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
概要：Kan 値 weighted nerve の射影の left fibration 性。
方針：最後の係数値で充填した単体を初区間へ追加し、全ての指定面の一致を使って戻す。
規約：元の通常の圏の対象と射の宇宙は u、係数も SSet.{u} に取る。
使われ方：Kerodon §5.3.3、strict transport の weighted nerve からの left fibration の復元。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：weighted nerve の相対左ホーンは最後の係数値が Kan なら充填できる。
方針：構成した候補の全ての面の一致を Yoneda の表示で単体集合の射へ戻す。
規約：必要な Kan 性は指定した底の射列の最後の値だけ。
使われ方：Kerodon §5.3.3、Kan 値 weighted nerve の左ホーンの持ち上げ。 -/
lemma exists_weightedNerve_leftHorn_lift {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    [KanComplex (F.obj (σ.obj (Fin.last (n + 1))))] (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    ∃ H : (Δ[n + 1] : SSet.{u}) ⟶ weightedNerve F,
      (horn (n + 1) k).ι ≫ H = a ∧ H ≫ weightedNerveProjection F = SSet.yonedaEquiv.symm σ := by
  obtain ⟨ψ, hp, ht⟩ := exists_weightedNerveHorn_candidate F σ k hk a ha
  let s : weightedNerveSimplex F (n + 1) := ⟨σ, ψ⟩
  let H : (Δ[n + 1] : SSet.{u}) ⟶ weightedNerve F := SSet.yonedaEquiv.symm s
  have hface (j : Fin (n + 2)) (hj : j ≠ k) : stdSimplex.δ j ≫ H = horn.ι k j hj ≫ a := by
    have he := weightedNerveHorn_candidate_face_agreement F σ k hk a ha ψ hp ht j hj
    calc
      _ = SSet.yonedaEquiv.symm (weightedNerveSimplexMap F (SimplexCategory.δ j) s) :=
        SSet.yonedaEquiv_symm_naturality_left (X := weightedNerve F) (SimplexCategory.δ j) s
      _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv (horn.ι k j hj ≫ a)) :=
        congrArg (SSet.yonedaEquiv (X := weightedNerve F) (n := ⦋n⦌)).symm he
      _ = _ := SSet.yonedaEquiv.symm_apply_apply _
  refine ⟨H, horn.hom_ext' hface, ?_⟩
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

/-- 概要：Kan 値の単体集合図式の weighted nerve の射影は left fibration。
方針：相対左ホーンの持ち上げを、指定した底の射列の最後の Kan 値で構成する。
規約：全ての正次元と最後以外の全ての欠ける面を扱う。
使われ方：Kerodon §5.3.3、通常の圏上の Kan 値表現からの left fibration の構成。 -/
instance weightedNerveProjection_leftFibration {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] : LeftFibration (weightedNerveProjection F) where
  mem := by
    intro A B i hi
    cases hi with
    | @intro n k hk =>
      constructor
      intro a b sq
      let σ := SSet.yonedaEquiv b
      have hb : SSet.yonedaEquiv.symm σ = b := SSet.yonedaEquiv.symm_apply_apply _
      have ha : a ≫ weightedNerveProjection F =
          (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ := by
        rw [hb]
        exact sq.w
      obtain ⟨H, hH, hHp⟩ := exists_weightedNerve_leftHorn_lift F σ k (ne_of_lt hk) a ha
      exact CommSq.HasLift.mk' { l := H, fac_left := hH, fac_right := hHp.trans hb }

/-- 概要：left fibration の strict transport の weighted nerve は同じ底上の left fibration。
方針：strict transport の各値の Kan 性を一般の weighted nerve の射影に適用する。
規約：元の全空間との同値は後続の scaffold の比較で示す。
使われ方：Kerodon §§5.3.3–5.3.5、strict transport 表現からの left fibration の復元候補。 -/
instance leftStrictTransportWeightedProjection_leftFibration
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    LeftFibration (leftStrictTransportWeightedProjection p) := by
  have (c : C) : KanComplex ((leftStrictTransportDiagram p).obj c) :=
    leftStrictTransport_kanComplex p c
  exact weightedNerveProjection_leftFibration (leftStrictTransportDiagram p)

/-- 概要：Kan 値 weighted nerve の全空間は quasicategory。
方針：底の通常の nerve の quasicategory 性と射影の inner fibration 性を使う。
規約：係数の各値に Kan 性を仮定する。
使われ方：Kerodon §5.3.3、weighted nerve の全空間を ∞ 圏として比較するための構造。 -/
instance weightedNerve_quasicategory {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] : Quasicategory (weightedNerve F) :=
  quasicategory_of_innerFibration (weightedNerveProjection F)

/-- 概要：left fibration の strict transport の weighted nerve の全空間は quasicategory。
方針：復元候補の射影の left fibration 性から inner fibration の全空間の判定を使う。
規約：通常の圏 C の nerve を底に取る。
使われ方：Kerodon §§5.3.3–5.3.5、元の全空間との ∞ 圏の比較の始域。 -/
instance leftStrictTransportWeightedNerve_quasicategory
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] : Quasicategory (leftStrictTransportWeightedNerve p) :=
  quasicategory_of_innerFibration (leftStrictTransportWeightedProjection p)

end SerrePositivity.InfinityCategories
