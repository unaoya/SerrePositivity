module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornResidual
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-! # 任意の dg 圏の dg nerve は quasicategory

概要：dg nerve の全ての内部ホーンは充填できる。
方針：明示的な補正データに主残差恒等式で最後の方程式を与え、米田対応でホーンを延長する。
規約：HA Proposition 1.3.1.10。使われ方：dg nerve 上のホモトピー圏と導来 ∞ 圏の基盤。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：任意の内部ホーンから、その全ての既知の面を持つ dg nerve の単体を構成する。
方針：補正データの欠けた面の方程式を主残差恒等式で証明したものを使う。
規約：HA Proposition 1.3.1.10。使われ方：内部ホーンの明示的な充填単体。 -/
def filler {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (h0 : 0 < i) (hlast : i < Fin.last (n + 2)) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) _⦋n + 2⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fillerOfMissingEquation σ h0 hlast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.fillerData_missing_equation σ h0 hlast)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (filler)


/-- 概要：明示的な充填単体の各既知の面は元のホーン面に一致する。
方針：充填候補の面への制限の検証を使う。
規約：HA Proposition 1.3.1.10。使われ方：ホーン充填と後続の低次計算。 -/
lemma filler_face {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (h0 : 0 < i) (hlast : i < Fin.last (n + 2)) (j : Fin (n + 3)) (hji : j ≠ i) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ j (filler A D σ h0 hlast) = σ.app _ (SSet.horn.face i j hji) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fillerOfMissingEquation_face σ h0 hlast _ j hji

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (filler_face)


/-- 概要：任意の内部ホーン写像は標準単体全体の写像へ延長できる。
方針：明示的な充填単体を米田対応で写像にし、ホーンの各面での一致で貼り合わせる。
規約：HA Proposition 1.3.1.10。使われ方：Mathlib の quasicategory 条件の充足。 -/
@[kerodon 00PW]
lemma hornFilling {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (h0 : 0 < i) (hlast : i < Fin.last (n + 2)) :
    ∃ τ : (Δ[n + 2] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D, σ = Λ[n + 2, i].ι ≫ τ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.extensionOfMissingEquation σ h0 hlast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.fillerData_missing_equation σ h0 hlast)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (hornFilling)


/-- 概要：任意の可換環上の dg 圏の dg nerve は quasicategory。
方針：全ての内部ホーンに明示的な延長を与える。
規約：HA Proposition 1.3.1.10。使われ方：ホモトピー圏・写像空間・導来 ∞ 圏への入口。 -/
@[kerodon 00PW]
instance instQuasicategory : SSet.Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) where
  hornFilling' _ _ σ h0 hlast := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hornFilling A D σ h0 hlast

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (instQuasicategory)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.1.10"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hornFilling
attribute [cite HA "1.3.1.10"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.instQuasicategory
