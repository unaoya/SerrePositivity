module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryCotensor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveIntervalBoundary

/-!
# 中断した任意モデル源への一般化：NerveBoundaryExtension

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Coherent higher parameter extensions with all whole facet systems fixed。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0464][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0464
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Coherent higher parameter extensions with all whole facet systems fixed
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveBoundaryExtension
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v}) {n : ℕ}

abbrev Compatible (faces : Fin (n + 3) → NerveParameterExtension.System F
    (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))) : Prop :=
  ∀ (j k : Fin (n + 3)) (hjk : j < k),
    faces j ≫ NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F
        (SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)))) =
    faces k ≫ NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F
        (SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk))))

variable (faces : Fin (n + 3) → NerveParameterExtension.System F
    (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))) (hf : Compatible F faces)

include hf in
lemma component_compatible (s : Index D) :
    BoundaryCotensor.Compatible (fun k => (faces k).app s) := by
  intro j k hjk
  exact congr_app (hf j k hjk) s

/-- Glue the actual boundary, retaining every already coherent facet in every degree. -/
def boundary : NerveParameterExtension.System F (SSet.boundary (n + 2)).toSSet where
  app s := BoundaryCotensor.standardDesc (fun k => (faces k).app s)
    (component_compatible F faces hf s)
  naturality {s t} f := by
    dsimp only [NerveCoherentFamily.values, NerveParameterExtension.cotensor, Functor.comp_map]
    apply BoundaryCotensor.hom_ext
    intro k
    simp only [Category.assoc, BoundaryCotensor.standardDesc_fac]
    rw [(pre (SSet.boundary.ι k)).naturality]
    rw [← Category.assoc, BoundaryCotensor.standardDesc_fac]
    exact (faces k).naturality f

lemma boundary_face (k : Fin (n + 3)) : boundary F faces hf ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.boundary.ι k)) = faces k := by
  apply NatTrans.ext
  funext s
  exact BoundaryCotensor.standardDesc_fac (fun k => (faces k).app s)
    (component_compatible F faces hf s) k

variable (old : ∀ d, SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 2)) ⟶ F.obj d)
  (hfaces : ∀ (k : Fin (n + 3)) (s : Lower (NerveCoherentFamily.reedy D) 1),
    (faces k).app s.obj = SSet.stdSimplex.isTerminalObj₀.from _ ≫
      RelativeChoiceSpace.name (SSet.stdSimplex.δ k ≫ old (endpoint s.obj)))

include hfaces in
lemma compatible : NerveParameterExtension.familyVertices F old ≫
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (NerveRelativeValueExtension.valueMap _ _
        (NerveParameterExtension.restriction F (SSet.boundary (n + 2)).ι)) =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (boundary F faces hf) := by
  apply NatTrans.ext
  funext s
  change (SSet.stdSimplex.isTerminalObj₀.from _ ≫
    RelativeChoiceSpace.name (old (endpoint s.obj))) ≫
      (pre (SSet.boundary (n + 2)).ι).app (F.obj (endpoint s.obj)) =
        (boundary F faces hf).app s.obj
  apply BoundaryCotensor.hom_ext
  intro k
  apply Eq.trans ?_ (BoundaryCotensor.standardDesc_fac
    (fun k => (faces k).app s.obj) (component_compatible F faces hf s.obj) k).symm
  rw [hfaces k s]
  have he : SSet.boundary.ι k ≫ (SSet.boundary (n + 2)).ι ≫ old (endpoint s.obj) =
      SSet.stdSimplex.δ k ≫ old (endpoint s.obj) := by rw [← Category.assoc, SSet.boundary.ι_ι]
  rw [← he, ← NerveIntervalBoundary.name_precomp, ← NerveIntervalBoundary.name_precomp]
  simp only [Category.assoc]

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hp : ∀ d, trivialFibrations SSet.{v} ((NerveCoherentExtension.projection F).app d))

/-- Keep the entire old higher simplex and every preselected whole coherent facet. -/
def extend : NerveParameterExtension.System F
    (SSet.stdSimplex.obj (SimplexCategory.mk (n + 2))) :=
  NerveParameterExtension.extendFamilies F hcof hfib hp (SSet.boundary (n + 2)).ι
    (boundary F faces hf) old (compatible F faces hf old hfaces)

lemma extend_evaluate (d : D) :
    NerveParameterExtension.evaluate F (extend F faces hf old hfaces hcof hfib hp) d = old d :=
  NerveParameterExtension.extendFamilies_evaluate _ _ _ _ _ _ _ _ d

lemma extend_restrict : Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
    (extend F faces hf old hfaces hcof hfib hp) = NerveParameterExtension.familyVertices F old :=
  NerveParameterExtension.extend_restrict F hcof hfib hp _ _ _ _ _

lemma extend_boundary : extend F faces hf old hfaces hcof hfib hp ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.boundary (n + 2)).ι) =
        boundary F faces hf := NerveParameterExtension.extendFamilies_boundary _ _ _ _ _ _ _ _

lemma extend_face (k : Fin (n + 3)) : extend F faces hf old hfaces hcof hfib hp ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.stdSimplex.δ k)) = faces k := by
  rw [← SSet.boundary.ι_ι k, NerveIntervalBoundary.restriction_comp]
  change _ ≫ (NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.boundary (n + 2)).ι) ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.boundary.ι k))) = _
  rw [← Category.assoc, extend_boundary, boundary_face]

end SerrePositivity.SimplicialModel.NerveBoundaryExtension
