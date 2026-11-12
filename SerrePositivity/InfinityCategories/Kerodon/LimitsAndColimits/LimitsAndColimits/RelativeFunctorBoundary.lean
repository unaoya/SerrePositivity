module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeBoundaryFamily
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeInternalHomTrivialFibration

/-!
概要：部分図式を固定する相対内部 Hom で、点ごとの相対始対象性・終対象性を判定する。
方針：持ち上げ問題の二成分を uncurry し、指定部分を保つ境界の族の充填を使う。
規約：標的の射や部分図式に fibration 性を要求しない。
使われ方：Kan 拡張の写像空間の制限で用いる相対的な関手圏の充填。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：全ての値が相対始対象である図式は、部分図式も固定した相対内部 Hom の相対始対象。
方針：pullback への単体を指定部分上の族と標的の族に分解し、両方を保って境界を充填する。
規約：A は任意の部分単体集合、X・Y・K は任意。
使われ方：Kerodon §7.1.8（Tag 02X8） の相対充填を Kan 拡張の関手圏の制限に利用する。 -/
lemma initialBoundaryLifting_relativeFunctor_of_pointwise {K X Y : SSet.{u}}
    (A : K.Subcomplex) (p : X ⟶ Y) (sq' : internalHom.PullbackObjObj A.ι p)
    (f : K ⟶ X)
    (hf : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p (f.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting sq'.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
  intro n b β hb sq
  have hfst : b ≫ (pre A.ι).app X = (boundary (n + 1)).ι ≫ (β ≫ sq'.fst) := by
    have h := congrArg (fun q ↦ q ≫ sq'.fst) sq.w
    rw [Category.assoc, sq'.π_fst, Category.assoc] at h
    change b ≫ (pre A.ι).app X = (boundary (n + 1)).ι ≫ β ≫ sq'.fst at h
    exact h
  have hsnd : b ≫ (ihom K).map p = (boundary (n + 1)).ι ≫ (β ≫ sq'.snd) := by
    have h := congrArg (fun q ↦ q ≫ sq'.snd) sq.w
    rw [Category.assoc, sq'.π_snd, Category.assoc] at h
    change b ≫ (ihom K).map p = (boundary (n + 1)).ι ≫ β ≫ sq'.snd at h
    exact h
  have hba := congrArg uncurry hfst
  rw [uncurry_pre_app, uncurry_natural_left] at hba
  have hbp := congrArg uncurry hsnd
  rw [uncurry_natural_right, uncurry_natural_left] at hbp
  have htarget : (β ≫ sq'.fst) ≫ (ihom (A : SSet.{u})).map p =
      (β ≫ sq'.snd) ≫ (pre A.ι).app Y := by
    have h := congrArg (fun q ↦ β ≫ q) sq'.isPullback.w
    change β ≫ ((sq'.fst ≫ (ihom (A : SSet.{u})).map p)) =
      β ≫ (sq'.snd ≫ (pre A.ι).app Y) at h
    exact h
  have hap := congrArg uncurry htarget
  rw [uncurry_natural_right, uncurry_pre_app] at hap
  obtain ⟨F, hF, hFA, hFp⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanInitialBoundaryFamily_lift_relative p A n f b (uncurry (β ≫ sq'.fst))
      (uncurry (β ≫ sq'.snd)) hb hba hbp hap hf
  refine ⟨curry F, ?_, ?_⟩
  · apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    exact hF
  · apply sq'.hom_ext
    · rw [Category.assoc, sq'.π_fst]
      change curry F ≫ (pre A.ι).app X = β ≫ sq'.fst
      apply uncurry_injective
      rw [uncurry_pre_app, uncurry_curry]
      exact hFA
    · rw [Category.assoc, sq'.π_snd]
      change curry F ≫ (ihom K).map p = β ≫ sq'.snd
      apply uncurry_injective
      rw [uncurry_natural_right, uncurry_curry]
      exact hFp

/-- 概要：全ての値が相対終対象である図式は、部分図式も固定した相対内部 Hom の相対終対象。
方針：pullback への単体を指定部分上の族と標的の族に分解し、両方を保って境界を充填する。
規約：A は任意の部分単体集合、X・Y・K は任意。
使われ方：Kerodon §7.1.8（Tag 02X8） の相対充填を Kan 拡張の関手圏の制限に利用する。 -/
lemma terminalBoundaryLifting_relativeFunctor_of_pointwise {K X Y : SSet.{u}}
    (A : K.Subcomplex) (p : X ⟶ Y) (sq' : internalHom.PullbackObjObj A.ι p)
    (f : K ⟶ X)
    (hf : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p (f.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting sq'.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
  intro n b β hb sq
  have hfst : b ≫ (pre A.ι).app X = (boundary (n + 1)).ι ≫ (β ≫ sq'.fst) := by
    have h := congrArg (fun q ↦ q ≫ sq'.fst) sq.w
    rw [Category.assoc, sq'.π_fst, Category.assoc] at h
    change b ≫ (pre A.ι).app X = (boundary (n + 1)).ι ≫ β ≫ sq'.fst at h
    exact h
  have hsnd : b ≫ (ihom K).map p = (boundary (n + 1)).ι ≫ (β ≫ sq'.snd) := by
    have h := congrArg (fun q ↦ q ≫ sq'.snd) sq.w
    rw [Category.assoc, sq'.π_snd, Category.assoc] at h
    change b ≫ (ihom K).map p = (boundary (n + 1)).ι ≫ β ≫ sq'.snd at h
    exact h
  have hba := congrArg uncurry hfst
  rw [uncurry_pre_app, uncurry_natural_left] at hba
  have hbp := congrArg uncurry hsnd
  rw [uncurry_natural_right, uncurry_natural_left] at hbp
  have htarget : (β ≫ sq'.fst) ≫ (ihom (A : SSet.{u})).map p =
      (β ≫ sq'.snd) ≫ (pre A.ι).app Y := by
    have h := congrArg (fun q ↦ β ≫ q) sq'.isPullback.w
    change β ≫ ((sq'.fst ≫ (ihom (A : SSet.{u})).map p)) =
      β ≫ (sq'.snd ≫ (pre A.ι).app Y) at h
    exact h
  have hap := congrArg uncurry htarget
  rw [uncurry_natural_right, uncurry_pre_app] at hap
  obtain ⟨F, hF, hFA, hFp⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanTerminalBoundaryFamily_lift_relative p A n f b (uncurry (β ≫ sq'.fst))
      (uncurry (β ≫ sq'.snd)) hb hba hbp hap hf
  refine ⟨curry F, ?_, ?_⟩
  · apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    exact hF
  · apply sq'.hom_ext
    · rw [Category.assoc, sq'.π_fst]
      change curry F ≫ (pre A.ι).app X = β ≫ sq'.fst
      apply uncurry_injective
      rw [uncurry_pre_app, uncurry_curry]
      exact hFA
    · rw [Category.assoc, sq'.π_snd]
      change curry F ≫ (ihom K).map p = β ≫ sq'.snd
      apply uncurry_injective
      rw [uncurry_natural_right, uncurry_curry]
      exact hFp

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
