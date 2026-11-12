module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.FixedBoundaryExtensions

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveRelativeValueExtension
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceSpace

/-!
# 中断した任意モデル源への一般化：NerveParameterExtension

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Coherent parameter extensions retaining prescribed families and coherent boundaries。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0487][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0487
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Coherent parameter extensions retaining prescribed families and coherent boundaries

A monomorphism of parameter spaces induces a pointwise trivial fibration
of cotensor diagrams. The entire coherent boundary system and every
specified lower-degree parameter family are retained simultaneously.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed HomotopicalAlgebra
open SerrePositivity.NerveSimplexEndpoint
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveParameterExtension
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

abbrev cotensor (K : SSet.{v}) : D ⥤ SSet.{v} := F ⋙ ihom K
abbrev System (K : SSet.{v}) := NerveCoherentFamily.System (cotensor F K)

abbrev restriction {A K : SSet.{v}} (i : A ⟶ K) : cotensor F K ⟶ cotensor F A :=
  Functor.whiskerLeft F (MonoidalClosed.internalHom.map i.op)

/-- Decode the entire actual parameter family at an original object. -/
abbrev evaluate {K : SSet.{v}} (a : System F K) (d : D) : K ⟶ F.obj d :=
  uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫ a.app (ofChain (ComposableArrows.mk₀ d)))

lemma name_evaluate {K : SSet.{v}} (a : System F K) (d : D) :
    RelativeChoiceSpace.name (evaluate F a d) = a.app (ofChain (ComposableArrows.mk₀ d)) := by
  simp only [evaluate, RelativeChoiceSpace.name, curry'_uncurry', Iso.hom_inv_id_assoc]

lemma name_injective {K P : SSet.{v}} {f g : K ⟶ P}
    (h : RelativeChoiceSpace.name f = RelativeChoiceSpace.name g) : f = g := by
  apply curry'_injective
  exact (cancel_epi RelativeChoiceSpace.pointUnitIso.hom).mp h

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hp : ∀ d, trivialFibrations SSet.{v} ((NerveCoherentExtension.projection F).app d))

include hcof hfib hp in
lemma restriction_trivialFibration {A K : SSet.{v}} (i : A ⟶ K) [Mono i] (d : D) :
    trivialFibrations SSet.{v} ((restriction F i).app d) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.restriction_trivialFibration hcof hfib i
    ((NerveCoherentExtension.projection F).app d) (hp d)

variable {A K : SSet.{v}} (i : A ⟶ K) [Mono i]
  (boundary : System F A) (n : ℕ) (old : NerveLowerExtension.LowerSystem (cotensor F K) n)
  (hboundary : old ≫ Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (NerveRelativeValueExtension.valueMap (cotensor F K) (cotensor F A) (restriction F i)) =
      Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n) boundary)

/-- Extend all chain directions, fixing the coherent parameter boundary in every degree. -/
def extend : System F K :=
  NerveRelativeValueExtension.extend (cotensor F K) (cotensor F A) (restriction F i)
    boundary n old hboundary (restriction_trivialFibration F hcof hfib hp i) hcof

lemma extend_boundary : extend F hcof hfib hp i boundary n old hboundary ≫
    NerveRelativeValueExtension.valueMap (cotensor F K) (cotensor F A) (restriction F i) =
      boundary :=
  NerveRelativeValueExtension.extend_boundary _ _ _ _ _ _ _ _ _

lemma extend_restrict : Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (extend F hcof hfib hp i boundary n old hboundary) = old :=
  NerveRelativeValueExtension.extend_restrict _ _ _ _ _ _ _ _ _

lemma extend_component (s : Lower (NerveCoherentFamily.reedy D) n) :
    (extend F hcof hfib hp i boundary n old hboundary).app s.obj = old.app s :=
  congr_app (extend_restrict F hcof hfib hp i boundary n old hboundary) s

lemma extend_evaluate (d : D) (hn : 0 < n) (e : K ⟶ F.obj d)
    (he : old.app ⟨ofChain (ComposableArrows.mk₀ d), hn⟩ = RelativeChoiceSpace.name e) :
    evaluate F (extend F hcof hfib hp i boundary n old hboundary) d = e := by
  change uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
    (extend F hcof hfib hp i boundary n old hboundary).app
      (ofChain (ComposableArrows.mk₀ d))) = e
  rw [extend_component F hcof hfib hp i boundary n old hboundary
    ⟨ofChain (ComposableArrows.mk₀ d), hn⟩, he]
  simp only [RelativeChoiceSpace.name, Iso.inv_hom_id_assoc, uncurry'_curry']

lemma evaluate_boundary (d : D) :
    i ≫ evaluate F (extend F hcof hfib hp i boundary n old hboundary) d =
      evaluate F boundary d := by
  apply name_injective
  rw [← RelativeChoiceSpace.name_precomp, name_evaluate, name_evaluate]
  exact congr_app (extend_boundary F hcof hfib hp i boundary n old hboundary)
    (ofChain (ComposableArrows.mk₀ d))

abbrev familyVertices (families : ∀ d, K ⟶ F.obj d) :
    NerveLowerExtension.LowerSystem (cotensor F K) 1 :=
  NerveLowerExtension.vertices (cotensor F K) (fun d => RelativeChoiceSpace.name (families d))

variable (families : ∀ d, K ⟶ F.obj d)
  (hfamilies : familyVertices F families ≫
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (NerveRelativeValueExtension.valueMap (cotensor F K) (cotensor F A) (restriction F i)) =
        Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1) boundary)

/-- Retain independently prescribed whole parameter families at every object. -/
def extendFamilies : System F K :=
  extend F hcof hfib hp i boundary 1 (familyVertices F families) hfamilies

lemma extendFamilies_evaluate (d : D) :
    evaluate F (extendFamilies F hcof hfib hp i boundary families hfamilies) d = families d :=
  extend_evaluate F hcof hfib hp i boundary 1 (familyVertices F families) hfamilies d
    Nat.zero_lt_one (families d)
    (NerveLowerExtension.vertices_component (cotensor F K)
      (fun d => RelativeChoiceSpace.name (families d)) d)

lemma extendFamilies_boundary : extendFamilies F hcof hfib hp i boundary families hfamilies ≫
    NerveRelativeValueExtension.valueMap (cotensor F K) (cotensor F A) (restriction F i) =
      boundary :=
  extend_boundary F hcof hfib hp i boundary 1 (familyVertices F families) hfamilies

end SerrePositivity.SimplicialModel.NerveParameterExtension
