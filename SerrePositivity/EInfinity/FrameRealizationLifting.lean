module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Realization
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

/-!
# Frame の実現の単射・anodyne 射に沿う持ち上げ

概要：Hovey §5.4 の実現が単射を cofibration、anodyne 射を trivial cofibration に移す。
方針：実際の随伴で持ち上げを移し、境界・ホーンの持ち上げ定理を使う。
規約：単体集合の完全なモデル構造は仮定しない。
使われ方：E 代数の右 frame の余テンソルの fibration 判定。
-/

@[expose] public section

noncomputable section

universe v u

namespace SerrePositivity.EInfinity.FrameRealizationLifting

open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open scoped SSet.modelCategoryQuillen

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{0, v} C] [ModelCategory C]
  (B : SimplexCategory ⥤ C)
  (hB : reedyLeft simplex (cofibrations C) (initial.to B))

include hB

/-- 概要：Reedy cofibrant な frame の実現は単射を cofibration へ移す（Hovey §5.4）。
方針：trivial fibration に対する随伴の持ち上げと境界生成類を使う。
規約：単体集合の側には単射のクラスだけを使う。
使われ方：余テンソルの単射に沿う fibration の証明。 -/
lemma map_monomorphism {K L : SSet.{v}} (i : K ⟶ L) (hi : Mono i) :
    cofibrations C ((Realization.functor B).map i) := by
  rw [← trivialFibrations_llp]
  intro Y Z p hp
  have : Fibration p := ⟨hp.1⟩
  have : WeakEquivalence p := ⟨hp.2⟩
  apply ((Realization.adjunction B).hasLiftingProperty_iff i p).mpr
  have h : (MorphismProperty.monomorphisms SSet.{v}).rlp ((cosimplicialHom B).map p) := by
    rw [SSet.rlp_monomorphisms]
    intro X Y f hf
    obtain ⟨n⟩ := hf
    exact boundary_lifting_of_reedyCofibrant B n hB p
  exact h i hi

/-- 概要：frame の実現は anodyne 射を trivial cofibration へ移す（Hovey §5.4）。
方針：任意の fibration に対するホーンの持ち上げを anodyne の左類へ拡張する。
規約：元の圏のモデル構造だけを使い、単体集合のモデル存在は不要。
使われ方：余テンソルの anodyne 射に沿う自明 fibration の証明。 -/
lemma map_anodyne
    (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    {K L : SSet.{v}} (i : K ⟶ L) (hi : SSet.anodyneExtensions i) :
    trivialCofibrations C ((Realization.functor B).map i) := by
  rw [← fibrations_llp]
  intro Y Z p hp
  have : Fibration p := ⟨hp⟩
  apply ((Realization.adjunction B).hasLiftingProperty_iff i p).mpr
  have h : Fibration ((cosimplicialHom B).map p) :=
    cosimplicialHom_fibration B hB hconst p
  exact hi _ ((SSet.modelCategoryQuillen.fibration_iff _).mp h)

end SerrePositivity.EInfinity.FrameRealizationLifting
