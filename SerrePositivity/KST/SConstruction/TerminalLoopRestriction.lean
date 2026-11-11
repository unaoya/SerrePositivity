module
public import SerrePositivity.KST.SConstruction.TerminalLoopHomotopyFiber
public import SerrePositivity.KST.SConstruction.TerminalPathEvaluation

/-! # 元の円の評価と終点固定 path への制限
概要：元の円の区間上の評価を保つ loop の族は、同じ終点固定 path の族を与える。
方針：元の商射との可換性と通常の curry の単射性で検出する。
規約：区間の向きを変えない。使われ方：元の零行 loop と終点固定 fiber 比較の厳密な接続。
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

/-- 終点基点の元の区間から元の円への点つき商射。 -/
def terminalIntervalToCircle : terminalPointedInterval.{u} ⟶ PointedSimplicialSet.circle.{u} :=
  pointedCofiberProjection terminalIntervalStart.{u} ≫ terminalEndpointCircleIso.{u}.hom

/-- 終点基点の区間から円への基礎射は元の円の商射。 -/
lemma terminalIntervalToCircle_right : terminalIntervalToCircle.{u}.right =
    PointedObject.cofiberQuotient (boundary.{u} 1).ι :=
  terminalEndpointCircleIso_quotient

/-- fiber 表示の path 成分の制限は元の円の商による制限そのもの。 -/
lemma loopTerminalRestriction_eq (B : PointedSimplicialSet.{u}) :
    (loopToTerminalEndpointHomIso B).hom ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection terminalIntervalStart.{u}) B =
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed terminalIntervalToCircle.{u} B := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  change (MonoidalClosed.pre terminalEndpointCircleIso.{u}.hom).app B ≫
    (MonoidalClosed.pre (pointedCofiberProjection terminalIntervalStart.{u})).app B = _
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map]
  rfl

/-- 元の円の区間評価を共有する loop と区間族は同じ終点固定 path 族を与える。 -/
lemma loopTerminalRestriction_family {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (l : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right) (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right) (h₁)
    (hl : (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷ A) ≫
      uncurry (l ≫ PointedObject.basedHomι PointedSimplicialSet.circle.{u} B) =
        (β_ (Δ[1] : SSet.{u}) A).hom ≫ h) :
    l ≫ ((loopToTerminalEndpointHomIso B).hom ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection terminalIntervalStart.{u}) B).right =
        terminalPathFamily B h h₁ := by
  rw [loopTerminalRestriction_eq]
  apply (cancel_mono (PointedObject.basedHomι terminalPointedInterval B)).mp
  change (l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre terminalIntervalToCircle B) ≫ _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc,
    terminalPathFamily_ι]
  apply uncurry_injective
  rw [uncurry_pre_app, terminalIntervalToCircle_right, uncurry_curry]
  exact hl

end SerrePositivity.KST.SConstruction
