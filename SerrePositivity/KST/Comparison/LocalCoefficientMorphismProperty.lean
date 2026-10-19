module

public import SerrePositivity.KST.Comparison.LocalCoefficientColimits
public import SerrePositivity.KST.Comparison.MorphismPropertyColimits

/-!
# 基底上の局所係数ホモロジー同型の閉性

概要：固定した局所係数での同型性の余積・filtered colimit・retract 閉性を証明する。
方針：構成済みの鎖複体とホモロジー関手の余極限保存を適用する。
規約：Weibel K-book IV.1.6。局所係数は固定した基底から引き戻す。
使われ方：基底上の horn セルの超限合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits

/--
概要：基底上の局所係数ホモロジーの関手。
方針：実際の正規化鎖複体をホモロジーで評価する。
規約：次数は非負整数。
使われ方：射の性質と余極限保存。
-/
abbrev overLocalHomologyFunctor {B : SSet.{u}} (L : LocalCoefficientSystem B) (n : ℕ) :=
  overLocalCoefficientChainsFunctor L ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n

/--
概要：固定した基底の局所係数で全次数の同型を誘導する射の性質。
方針：実際のホモロジー関手による同型の逆像の交わり。
規約：全ての対象で基底から係数を引き戻す。
使われ方：horn セル表示への閉性の適用。
-/
abbrev overLocalHomologyEquivalences {B : SSet.{u}} (L : LocalCoefficientSystem B) :
    MorphismProperty (Over B) :=
  ⨅ n : ℕ, (MorphismProperty.isomorphisms AddCommGrpCat.{u}).inverseImage
    (overLocalHomologyFunctor L n)

/--
概要：局所係数ホモロジー同型は実際の鎖写像の擬同型性と同値である。
方針：擬同型と各次数のホモロジー同型の定義を展開する。
規約：正規化鎖複体。
使われ方：pushout の鎖複体の定理との接続。
-/
theorem overLocalHomologyEquivalences_iff {B : SSet.{u}} (L : LocalCoefficientSystem B)
    {X Y : Over B} (f : X ⟶ Y) :
    overLocalHomologyEquivalences L f ↔ QuasiIso ((overLocalCoefficientChainsFunctor L).map f) := by
  simp only [overLocalHomologyEquivalences, MorphismProperty.iInf_iff,
    MorphismProperty.inverseImage, MorphismProperty.isomorphisms]
  rw [quasiIso_iff]
  exact forall_congr' (fun n => (quasiIsoAt_iff_isIso_homologyMap _ n).symm)

instance overLocalHomologyEquivalences_isMultiplicative {B : SSet.{u}}
    (L : LocalCoefficientSystem B) : (overLocalHomologyEquivalences L).IsMultiplicative := by
  dsimp only [overLocalHomologyEquivalences]
  infer_instance

instance overLocalHomologyEquivalences_respectsIso {B : SSet.{u}}
    (L : LocalCoefficientSystem B) : (overLocalHomologyEquivalences L).RespectsIso := by
  dsimp only [overLocalHomologyEquivalences]
  infer_instance

instance overLocalHomologyEquivalences_stableRetracts {B : SSet.{u}}
    (L : LocalCoefficientSystem B) : (overLocalHomologyEquivalences L).IsStableUnderRetracts where
  of_retract {X Y Z W f g} h hg := by
    simp only [overLocalHomologyEquivalences, MorphismProperty.iInf_iff] at hg ⊢
    intro n
    exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms AddCommGrpCat)
      (h.map (overLocalHomologyFunctor L n)) (hg n)

instance overLocalHomology_preservesExactColimits {B : SSet.{u}}
    (L : LocalCoefficientSystem B) {J : Type u} [Category.{u} J]
    [HasExactColimitsOfShape J AddCommGrpCat.{u}] (n : ℕ) :
    PreservesColimitsOfShape J (overLocalHomologyFunctor L n) := by
  dsimp only [overLocalHomologyFunctor]
  infer_instance

instance overLocalHomologyEquivalences_stableColimits {B : SSet.{u}}
    (L : LocalCoefficientSystem B) {J : Type*} [Category* J]
    [∀ n : ℕ, PreservesColimitsOfShape J (overLocalHomologyFunctor L n)] :
    (overLocalHomologyEquivalences L).IsStableUnderColimitsOfShape J where
  condition F G cF cG hcF hcG α hα f hf := by
    simp only [overLocalHomologyEquivalences, MorphismProperty.iInf_iff]
    have hn (j) (n : ℕ) :
        (MorphismProperty.isomorphisms AddCommGrpCat.{u}).inverseImage
          (overLocalHomologyFunctor L n) (α.app j) := by
      have hj := hα j
      simp only [overLocalHomologyEquivalences, MorphismProperty.iInf_iff] at hj
      exact hj n
    intro n
    have := morphismProperty_inverseImage_stableColimits
      (MorphismProperty.isomorphisms AddCommGrpCat.{u}) (overLocalHomologyFunctor L n) J
    exact MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := (MorphismProperty.isomorphisms AddCommGrpCat.{u}).inverseImage
        (overLocalHomologyFunctor L n)) F G cF cG hcF hcG α
      (fun j => hn j n) f hf

instance overLocalHomologyEquivalences_stableCoproducts {B : SSet.{u}}
    (L : LocalCoefficientSystem B) :
    MorphismProperty.IsStableUnderCoproducts.{u} (overLocalHomologyEquivalences L) where

instance overLocalHomologyEquivalences_stableFilteredColimits {B : SSet.{u}}
    (L : LocalCoefficientSystem B) :
    MorphismProperty.IsStableUnderFilteredColimits.{u, u} (overLocalHomologyEquivalences L) where
  isStableUnderColimitsOfShape J _ _ := by infer_instance

/--
概要：基底上の射の台が単射である性質。
方針：忘却関手による単射の逆像を取る。
規約：基底上の単射性とも同値。
使われ方：horn の余積が単射であることの確認。
-/
abbrev overUnderlyingMonomorphisms (B : SSet.{u}) : MorphismProperty (Over B) :=
  (MorphismProperty.monomorphisms SSet.{u}).inverseImage (Over.forget B)

instance overUnderlyingMonomorphisms_stableCoproducts (B : SSet.{u}) :
    MorphismProperty.IsStableUnderCoproducts.{u} (overUnderlyingMonomorphisms B) where
  isStableUnderCoproductsOfShape J :=
    morphismProperty_inverseImage_stableColimits _ _ (Discrete J)

end SerrePositivity.KST.Comparison
