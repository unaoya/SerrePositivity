module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryOneCotensor
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveParameterExtension

/-!
# 中断した任意モデル源への一般化：NerveIntervalBoundary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Coherent interval boundaries glued from two whole endpoint systems。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0475][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0475
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Coherent interval boundaries glued from two whole endpoint systems
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveIntervalBoundary
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

/-- Regard a coherent system as constant in a supplementary parameter. -/
def constant (K : SSet.{v}) (a : NerveCoherentFamily.System F) :
    NerveParameterExtension.System F K where
  app s := curry (snd K _ ≫ a.app s)
  naturality {s t} f := by
    dsimp only [NerveCoherentFamily.values, NerveParameterExtension.cotensor, Functor.comp_map]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_natural_right, uncurry_curry]
    rw [← Category.assoc, whiskerLeft_snd, Category.assoc, a.naturality]
    rfl

lemma constant_point (a : NerveCoherentFamily.System F)
    (points : ∀ d, BoundaryOneCotensor.vertex ⟶ F.obj d)
    (s : Lower (NerveCoherentFamily.reedy D) 1)
    (ha : a.app s.obj = SSet.stdSimplex.isTerminalObj₀.from _ ≫ points (endpoint s.obj)) :
    (constant F BoundaryOneCotensor.vertex a).app s.obj =
      SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.name (points (endpoint s.obj)) := by
  change curry (snd _ _ ≫ a.app s.obj) = _
  apply uncurry_injective
  rw [uncurry_natural_left, RelativeChoiceSpace.name, uncurry_natural_left]
  dsimp only [curry']
  rw [uncurry_curry, uncurry_curry, ha]
  have ht : snd BoundaryOneCotensor.vertex ((NerveCoherentFamily.simplices D).obj s.obj) ≫
      SSet.stdSimplex.isTerminalObj₀.from _ =
      BoundaryOneCotensor.vertex ◁ SSet.stdSimplex.isTerminalObj₀.from
        ((NerveCoherentFamily.simplices D).obj s.obj) ≫
      BoundaryOneCotensor.vertex ◁ RelativeChoiceSpace.pointUnitIso.hom ≫
        (ρ_ BoundaryOneCotensor.vertex).hom :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ points (endpoint s.obj)) ht

/-- Glue the two independently specified endpoint systems in all external degrees. -/
def boundary (a b : NerveCoherentFamily.System F) :
    NerveParameterExtension.System F BoundaryOneCotensor.boundary where
  app s := BoundaryOneCotensor.glue
    ((constant F BoundaryOneCotensor.vertex a).app s)
    ((constant F BoundaryOneCotensor.vertex b).app s)
  naturality {s t} f := by
    dsimp only [NerveCoherentFamily.values, NerveParameterExtension.cotensor, Functor.comp_map]
    apply BoundaryOneCotensor.hom_ext
    · simp only [Category.assoc, BoundaryOneCotensor.glue_zero]
      rw [(pre BoundaryOneCotensor.zero).naturality]
      rw [← Category.assoc, BoundaryOneCotensor.glue_zero]
      exact (constant F BoundaryOneCotensor.vertex a).naturality f
    · simp only [Category.assoc, BoundaryOneCotensor.glue_one]
      rw [(pre BoundaryOneCotensor.one).naturality]
      rw [← Category.assoc, BoundaryOneCotensor.glue_one]
      exact (constant F BoundaryOneCotensor.vertex b).naturality f

lemma boundary_zero (a b : NerveCoherentFamily.System F) : boundary F a b ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F BoundaryOneCotensor.zero) =
        constant F BoundaryOneCotensor.vertex a := by
  apply NatTrans.ext
  funext s
  exact BoundaryOneCotensor.glue_zero _ _

lemma boundary_one (a b : NerveCoherentFamily.System F) : boundary F a b ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F BoundaryOneCotensor.one) =
        constant F BoundaryOneCotensor.vertex b := by
  apply NatTrans.ext
  funext s
  exact BoundaryOneCotensor.glue_one _ _

lemma name_precomp {A K P : SSet.{v}} (i : A ⟶ K) (e : K ⟶ P) :
    RelativeChoiceSpace.name e ≫ (pre i).app P = RelativeChoiceSpace.name (i ≫ e) :=
  RelativeChoiceSpace.name_precomp i e

variable (a b : NerveCoherentFamily.System F)
  (p₀ p₁ : ∀ d, BoundaryOneCotensor.vertex ⟶ F.obj d)
  (ha : ∀ s : Lower (NerveCoherentFamily.reedy D) 1,
    a.app s.obj = SSet.stdSimplex.isTerminalObj₀.from _ ≫ p₀ (endpoint s.obj))
  (hb : ∀ s : Lower (NerveCoherentFamily.reedy D) 1,
    b.app s.obj = SSet.stdSimplex.isTerminalObj₀.from _ ≫ p₁ (endpoint s.obj))
  (edges : ∀ d, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ F.obj d)
  (h₀ : ∀ d, SSet.stdSimplex.δ (1 : Fin 2) ≫ edges d = p₀ d)
  (h₁ : ∀ d, SSet.stdSimplex.δ (0 : Fin 2) ≫ edges d = p₁ d)

include p₀ p₁ ha hb h₀ h₁ in
/-- Endpoint equations imply the complete low-degree boundary compatibility. -/
lemma compatible : NerveParameterExtension.familyVertices F edges ≫
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (NerveRelativeValueExtension.valueMap _ _
        (NerveParameterExtension.restriction F (SSet.boundary 1).ι)) =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1) (boundary F a b) := by
  apply NatTrans.ext
  funext s
  change (SSet.stdSimplex.isTerminalObj₀.from _ ≫
    RelativeChoiceSpace.name (edges (endpoint s.obj))) ≫
      (pre (SSet.boundary 1).ι).app (F.obj (endpoint s.obj)) = (boundary F a b).app s.obj
  apply BoundaryOneCotensor.hom_ext
  · change (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.name (edges (endpoint s.obj)) ≫ (pre (SSet.boundary 1).ι).app _) ≫
        (pre BoundaryOneCotensor.zero).app _ = _
    apply Eq.trans ?_ (BoundaryOneCotensor.glue_zero
      ((constant F BoundaryOneCotensor.vertex a).app s.obj)
      ((constant F BoundaryOneCotensor.vertex b).app s.obj)).symm
    apply Eq.trans ?_ (constant_point F a p₀ s (ha s)).symm
    have he : BoundaryOneCotensor.zero ≫ (SSet.boundary 1).ι ≫
        edges (endpoint s.obj) = p₀ (endpoint s.obj) := by
      rw [← Category.assoc, SSet.boundary.ι_ι]
      exact h₀ _
    rw [← he, ← name_precomp, ← name_precomp]
    simp only [Category.assoc]
  · change (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.name (edges (endpoint s.obj)) ≫ (pre (SSet.boundary 1).ι).app _) ≫
        (pre BoundaryOneCotensor.one).app _ = _
    apply Eq.trans ?_ (BoundaryOneCotensor.glue_one
      ((constant F BoundaryOneCotensor.vertex a).app s.obj)
      ((constant F BoundaryOneCotensor.vertex b).app s.obj)).symm
    apply Eq.trans ?_ (constant_point F b p₁ s (hb s)).symm
    have he : BoundaryOneCotensor.one ≫ (SSet.boundary 1).ι ≫
        edges (endpoint s.obj) = p₁ (endpoint s.obj) := by
      rw [← Category.assoc, SSet.boundary.ι_ι]
      exact h₁ _
    rw [← he, ← name_precomp, ← name_precomp]
    simp only [Category.assoc]

lemma restriction_comp {A B K : SSet.{v}} (i : A ⟶ B) (j : B ⟶ K) :
    NerveParameterExtension.restriction F (i ≫ j) =
      NerveParameterExtension.restriction F j ≫ NerveParameterExtension.restriction F i := by
  apply NatTrans.ext
  funext d
  exact congr_app (MonoidalClosed.internalHom.map_comp j.op i.op) (F.obj d)


variable [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hp : ∀ d, HomotopicalAlgebra.trivialFibrations SSet.{v}
    ((NerveCoherentExtension.projection F).app d))

/-- Retain the entire old interval family with two prescribed coherent endpoint systems. -/
def extend : NerveParameterExtension.System F
    (SSet.stdSimplex.obj (SimplexCategory.mk 1)) :=
  NerveParameterExtension.extendFamilies F hcof hfib hp (SSet.boundary 1).ι
    (boundary F a b) edges (compatible F a b p₀ p₁ ha hb edges h₀ h₁)

lemma extend_evaluate (d : D) :
    NerveParameterExtension.evaluate F
      (extend F a b p₀ p₁ ha hb edges h₀ h₁ hcof hfib hp) d = edges d :=
  NerveParameterExtension.extendFamilies_evaluate _ _ _ _ _ _ _ _ d

lemma extend_boundary : extend F a b p₀ p₁ ha hb edges h₀ h₁ hcof hfib hp ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.boundary 1).ι) = boundary F a b :=
  NerveParameterExtension.extendFamilies_boundary _ _ _ _ _ _ _ _


lemma extend_zero : extend F a b p₀ p₁ ha hb edges h₀ h₁ hcof hfib hp ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.stdSimplex.δ (1 : Fin 2))) =
        constant F BoundaryOneCotensor.vertex a := by
  rw [← SSet.boundary.ι_ι (1 : Fin 2), restriction_comp]
  change _ ≫ (NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.boundary 1).ι) ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F BoundaryOneCotensor.zero)) = _
  rw [← Category.assoc, extend_boundary, boundary_zero]

lemma extend_one : extend F a b p₀ p₁ ha hb edges h₀ h₁ hcof hfib hp ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.stdSimplex.δ (0 : Fin 2))) =
        constant F BoundaryOneCotensor.vertex b := by
  rw [← SSet.boundary.ι_ι (0 : Fin 2), restriction_comp]
  change _ ≫ (NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.boundary 1).ι) ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F BoundaryOneCotensor.one)) = _
  rw [← Category.assoc, extend_boundary, boundary_one]

/-- A whole coherent system for the chosen endpoint points, independent of the interval filling. -/
abbrev chosenEndpoint (points : ∀ d, BoundaryOneCotensor.vertex ⟶ F.obj d) :=
  NerveLowerExtension.extendVertices F hp hcof points

/-- Prescribe endpoint points once and retain those same endpoint systems on every interval. -/
def betweenChosen : NerveParameterExtension.System F
    (SSet.stdSimplex.obj (SimplexCategory.mk 1)) :=
  extend F (chosenEndpoint F hcof hp p₀) (chosenEndpoint F hcof hp p₁) p₀ p₁
    (fun s => NerveLowerExtension.extend_component _ _ _ _ _ s)
    (fun s => NerveLowerExtension.extend_component _ _ _ _ _ s)
    edges h₀ h₁ hcof hfib hp

lemma betweenChosen_evaluate (d : D) :
    NerveParameterExtension.evaluate F
      (betweenChosen F p₀ p₁ edges h₀ h₁ hcof hfib hp) d = edges d :=
  extend_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ d

lemma betweenChosen_restrict :
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (betweenChosen F p₀ p₁ edges h₀ h₁ hcof hfib hp) =
        NerveParameterExtension.familyVertices F edges :=
  NerveParameterExtension.extend_restrict F hcof hfib hp _ _ _ _ _

lemma betweenChosen_zero : betweenChosen F p₀ p₁ edges h₀ h₁ hcof hfib hp ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.stdSimplex.δ (1 : Fin 2))) =
        constant F BoundaryOneCotensor.vertex (chosenEndpoint F hcof hp p₀) :=
  extend_zero _ _ _ _ _ _ _ _ _ _ _ _ _

lemma betweenChosen_one : betweenChosen F p₀ p₁ edges h₀ h₁ hcof hfib hp ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.stdSimplex.δ (0 : Fin 2))) =
        constant F BoundaryOneCotensor.vertex (chosenEndpoint F hcof hp p₁) :=
  extend_one _ _ _ _ _ _ _ _ _ _ _ _ _

/-- No supplied boundary or compatibility input is needed for arbitrary objectwise old intervals. -/
def ofEdges : NerveParameterExtension.System F
    (SSet.stdSimplex.obj (SimplexCategory.mk 1)) :=
  extend F
    (chosenEndpoint F hcof hp (fun d => SSet.stdSimplex.δ (1 : Fin 2) ≫ edges d))
    (chosenEndpoint F hcof hp (fun d => SSet.stdSimplex.δ (0 : Fin 2) ≫ edges d))
    (fun d => SSet.stdSimplex.δ (1 : Fin 2) ≫ edges d)
    (fun d => SSet.stdSimplex.δ (0 : Fin 2) ≫ edges d)
    (fun s => NerveLowerExtension.extend_component _ _ _ _ _ s)
    (fun s => NerveLowerExtension.extend_component _ _ _ _ _ s)
    edges (fun _ => rfl) (fun _ => rfl) hcof hfib hp

lemma ofEdges_evaluate (d : D) :
    NerveParameterExtension.evaluate F (ofEdges F edges hcof hfib hp) d = edges d :=
  extend_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ d

lemma ofEdges_zero : ofEdges F edges hcof hfib hp ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.stdSimplex.δ (1 : Fin 2))) =
        constant F BoundaryOneCotensor.vertex
          (chosenEndpoint F hcof hp (fun d => SSet.stdSimplex.δ (1 : Fin 2) ≫ edges d)) :=
  extend_zero _ _ _ _ _ _ _ _ _ _ _ _ _

lemma ofEdges_one : ofEdges F edges hcof hfib hp ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.stdSimplex.δ (0 : Fin 2))) =
        constant F BoundaryOneCotensor.vertex
          (chosenEndpoint F hcof hp (fun d => SSet.stdSimplex.δ (0 : Fin 2) ≫ edges d)) :=
  extend_one _ _ _ _ _ _ _ _ _ _ _ _ _

end SerrePositivity.SimplicialModel.NerveIntervalBoundary
