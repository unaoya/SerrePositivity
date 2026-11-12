module
public import SerrePositivity.KST.SConstruction.AnodyneExtensionChoices

/-! # 変化する anodyne 部分族の指定境界を保つ延長
概要：パラメータとともに部分図式が変わる場合にも、既存境界の全延長を厳密に保つ。
方針：部分図式の内部 Hom 制限の全単射 RLP を使い、実族として uncurry する。
規約：部分図式をパラメータ全体で定数と仮定せず、指定境界と指定部分の両方を保持する。
使われ方：元の K prism から復号した、二脚が変化するホーン族の相対貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra
open scoped Simplicial

/-- 変化する部分族を、元のパラメータ境界の全延長を厳密に保って延長する。 -/
def relativeAnodyneFamilyExtension {A B E T U : SSet.{u}} [KanComplex E]
    (i : A ⟶ B) (hi : anodyneExtensions i) (j : T ⟶ U) [Mono j]
    (Q : A ⊗ U ⟶ E) (R : B ⊗ T ⟶ E)
    (h : (i ▷ T) ≫ R = (A ◁ j) ≫ Q) :
    {L : B ⊗ U ⟶ E // (i ▷ U) ≫ L = Q ∧ (B ◁ j) ≫ L = R} := by
  let : HasLiftingProperty j ((pre i).app E) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyne_pre_rlp_monomorphisms i hi E j
    inferInstance
  let sq : CommSq (curry R) j ((pre i).app E) (curry Q) := ⟨by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_natural_left, uncurry_curry, uncurry_curry]
    exact h⟩
  refine ⟨uncurry sq.lift, ?_, ?_⟩
  · rw [← uncurry_pre_app, sq.fac_right, uncurry_curry]
  · rw [← uncurry_natural_left, sq.fac_left, uncurry_curry]

end SerrePositivity.KST.SConstruction
