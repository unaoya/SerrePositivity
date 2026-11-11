module
public import SerrePositivity.KST.Fibration.ClosedKernelCoefficient
public import SerrePositivity.KST.SConstruction.MultiRealizationFunctorIso

/-!
概要：元の P 全旗包含に沿う共通 cofiber の全関手比較。
方針：二つの元の補完の実底辺を厳密に照合し、充満忠実な射影で同型を戻す。
規約：補完を選び直さず、P 自身の同じ係数を保持する。
使われ方：有限旗の実積座標から全自然性の引き戻しを導く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
open Relative
variable {B : StableModel.{u}} (P : ClosedStablePredicate B)
  {n : SimplexCategory} (α : ⦋1⦌ ⟶ n)

/-- 概要：元の包含前後の二補完は同じ元の実底辺を厳密に持つ。
方針：両補完の底辺回収を同じ前合成と後合成の可換式へ戻す。
規約：全関手族の厳密等式。使われ方：充満忠実な射影から比較を戻す前提。 -/
theorem closedFlagCofiberPostcomparison_bottom :
    (closedKernelFlagPost P n ≫ closedFlagCofiberCompletion P α).val ≫
      closedCofiberRawProjection P =
        (weakStringCofiberExact (closedKernelZeroMap P) α ≫
          closedFlagKernelCofiberPost P).val ≫ closedCofiberRawProjection P := by
  have h₁ : (closedKernelFlagPost P n ≫ closedFlagCofiberCompletion P α).val ≫
      closedCofiberRawProjection P =
      (closedStableInclusion (weakStringClosedPredicate (closedKernelZeroMap P) n)).val ≫
        ((ihom (SSet.stdSimplex.obj n)).map (closedKernelInclusion P).hom ≫
          (pre (SSet.stdSimplex.map α)).app B.carrier) := by
    change ((closedKernelFlagPost P n).val ≫ (closedFlagCofiberCompletion P α).val) ≫ _ = _
    rw [Category.assoc, closedFlagCofiberCompletion_rawProjection, ← Category.assoc]
    rw [closedKernelFlagPost_inclusion, Category.assoc]
    rfl
  have h₂ : (weakStringCofiberExact (closedKernelZeroMap P) α ≫
      closedFlagKernelCofiberPost P).val ≫ closedCofiberRawProjection P =
      (closedStableInclusion (weakStringClosedPredicate (closedKernelZeroMap P) n)).val ≫
        ((pre (SSet.stdSimplex.map α)).app (closedStableModel P).carrier ≫
          (ihom (Δ[1] : SSet.{u})).map (closedKernelInclusion P).hom) := by
    change ((weakStringCofiberExact (closedKernelZeroMap P) α).val ≫
      (closedFlagKernelCofiberPost P).val) ≫ _ = _
    rw [Category.assoc, closedFlagKernelCofiberPost_rawProjection, ← Category.assoc,
      weakStringCofiberExact_rawProjection, Category.assoc]
    rfl
  exact h₁.trans ((congrArg (fun f =>
    (closedStableInclusion (weakStringClosedPredicate (closedKernelZeroMap P) n)).val ≫ f)
      ((pre (SSet.stdSimplex.map α)).naturality (closedKernelInclusion P).hom)).trans h₂.symm)

/-- 概要：元の包含前後の同じ cofiber 補完は全関手圏内で自然同型。
方針：同じ底辺の厳密一致を元の充満忠実な射影に沿って戻す。
規約：全入力族を保持。使われ方：P 値 cofiber 座標の自然性。 -/
def closedFlagCofiberPostcomparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (closedKernelFlagPost P n ≫ closedFlagCofiberCompletion P α).val
      (weakStringCofiberExact (closedKernelZeroMap P) α ≫ closedFlagKernelCofiberPost P).val := by
  apply (closedCofiberRawProjection_fullyFaithful P).preimageFunctorIso
  exact eqToIso (congrArg (fun f => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (closedFlagCofiberPostcomparison_bottom P α))

/-- 概要：元の包含前後の cofiber 係数は同じ P 自身に値を持つ全関手同型。
方針：同じ二補完の比較を quotient 頂点へ送り、元の係数同型を回収する。
規約：retract 閉包なし。使われ方：全有限積の局所化座標の比較。 -/
def closedFlagCofiber_postcomp :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (closedKernelFlagPost P n ≫ closedFlagCofiber P α).val
      (weakStringKernelCofiber (closedKernelZeroMap P) α ≫
        (closedFlagKernelCoefficientIso P).hom).val := by
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((closedKernelFlagPost P n ≫ closedFlagCofiberCompletion P α) ≫
        relativeCofiberQuotient (ClosedStablePredicate.top B) P).val
      ((weakStringCofiberExact (closedKernelZeroMap P) α ≫ closedFlagKernelCofiberPost P) ≫
        relativeCofiberQuotient (ClosedStablePredicate.top B) P).val :=
    (closedFlagCofiberPostcomparison P α).postcomp
      (relativeCofiberQuotient (ClosedStablePredicate.top B) P).val
  simpa only [closedFlagCofiber, weakStringKernelCofiber, Category.assoc,
    closedFlagKernelCofiberPost_quotient] using e

/-- 概要：同じ実包含に沿う P cofiber 比較は全正反復で局所化後に可換。
方針：元の全関手同型を正本の実現比較へ代入する。
規約：元の二つの実射を保持。使われ方：初期評価四角形の実積座標。 -/
theorem closedFlagCofiberMultiMap_postcomp (r : ℕ) :
    AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (closedKernelFlagPost P n ≫ closedFlagCofiber P α)) =
    AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (weakStringKernelCofiber (closedKernelZeroMap P) α ≫
        (closedFlagKernelCoefficientIso P).hom)) :=
  multiRealization_map_positive_localized_eq_of_functorIso r (closedFlagCofiber_postcomp P α)

end SerrePositivity.KST.Fibration
