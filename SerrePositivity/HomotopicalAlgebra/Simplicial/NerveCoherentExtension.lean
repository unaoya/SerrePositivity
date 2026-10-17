module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexInverseMatching
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.WeakFactorizationSystem

/-!
# 中断した任意モデル源への一般化：NerveCoherentExtension

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Relative coherent choice on every chain of a possibly large category。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0465][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0465
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative coherent choice on every chain of a possibly large category

The right condition is proved from contractible values and actual endpoint
transport. Relative Reedy cofibrations retain prescribed partial natural
systems. In particular the proved cofibrant simplex parameter gives a full
system without requiring a strictly natural choice of points.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.NerveSimplexEndpoint
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveCoherentExtension
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

/-- The actual canonical point projection; no choice of a section is assumed. -/
def projection : F ⟶ (Functor.const D).obj
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) where
  app _ := SSet.stdSimplex.isTerminalObj₀.from _
  naturality {_ _} _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

abbrev valueProjection := Functor.whiskerLeft (NerveSimplexEndpoint.functor D) (projection F)

variable [ModelCategory SSet.{v}]
  (hp : ∀ d, trivialFibrations SSet.{v} ((projection F).app d))

include hp in
lemma reedyRight : Reedy.reedyRight (NerveCoherentFamily.reedy D)
    (trivialFibrations SSet.{v}) (valueProjection F) :=
  SimplexInverseMatching.reedyRight (nerve D) (NerveCoherentFamily.values F) (valueProjection F)
    (fun f hf => by
      have := NerveCoherentFamily.endpointMap_isIso f hf
      exact Functor.map_isIso (F := F) _)
    (fun s => hp (endpoint s))

include hp in
lemma relative {B : Index D ⥤ SSet.{v}}
    (i : B ⟶ NerveCoherentFamily.simplices D)
    (hi : reedyLeft (NerveCoherentFamily.reedy D) (cofibrations SSet.{v}) i)
    (a : B ⟶ NerveCoherentFamily.values F) :
    ∃ b : NerveCoherentFamily.System F, i ≫ b = a := by
  have : HasLiftingProperty i (valueProjection F) :=
    lifting_of_reedy (NerveCoherentFamily.reedy D) (cofibrations SSet.{v})
      (trivialFibrations SSet.{v}) i (valueProjection F) hi (reedyRight F hp)
  have sq : CommSq a i (valueProjection F) (NerveCoherentFamily.collapse (D := D)) := by
    constructor
    apply NatTrans.ext
    funext s
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact ⟨sq.lift, sq.fac_left⟩

lemma parameterCofibrant
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _) :
    reedyLeft (NerveCoherentFamily.reedy D) (cofibrations SSet.{v})
      (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D)) :=
  SimplexLatchingBoundary.reedy_cofibrant (nerve D) hcof

include hp in
lemma exists_system (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _) :
    Nonempty (NerveCoherentFamily.System F) := by
  obtain ⟨b, _hb⟩ := relative F hp (B := ⊥_ (Index D ⥤ SSet.{v}))
    (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D))
    (parameterCofibrant (D := D) hcof)
    (initial.to (NerveCoherentFamily.values F))
  exact ⟨b⟩

variable {B : Index D ⥤ SSet.{v}} (i : B ⟶ NerveCoherentFamily.simplices D)
  (hi : reedyLeft (NerveCoherentFamily.reedy D) (cofibrations SSet.{v}) i)
  (a : B ⟶ NerveCoherentFamily.values F)

/-- Choose one whole extension, rather than independent fillers for the individual chains. -/
def extend : NerveCoherentFamily.System F := (relative F hp i hi a).choose

@[reassoc]
lemma extend_initial : i ≫ extend F hp i hi a = a := (relative F hp i hi a).choose_spec

lemma extend_component (s : Index D) : i.app s ≫ (extend F hp i hi a).app s = a.app s :=
  congr_app (extend_initial F hp i hi a) s

end SerrePositivity.SimplicialModel.NerveCoherentExtension
