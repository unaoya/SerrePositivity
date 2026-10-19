module
public import SerrePositivity.InfinityCategories.Derived.DGNerveUniverseMap
public import SerrePositivity.InfinityCategories.Derived.DGFunctorFullyFaithful
public import SerrePositivity.InfinityCategories.F1.UniverseInnerFibration
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus

/-! # 共通宇宙での dg 関手の nerve の充満忠実性

概要：対象宇宙が異なっても Hom 複体同型な dg 関手は実写像空間で充満忠実。
方針：対象を上げた同一宇宙の dg 関手へ分解し、両端の実同型で輸送する。
規約：h の充満忠実性だけでは判定しない。使われ方：dg Yoneda の全加群 nerve への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
variable [DGCategory A D] [DGCategory A E]

/-- 共通宇宙での nerve は対象を上げた dg 関手と両端の実同型へ分解できる。 -/
lemma dgNerveUniverseMap_factor (F : DGFunctor A D E) :
    dgNerveUniverseMap F = (dgNerveUniverseLiftIso.{u, v, w} A D).hom ≫
      dgNerve.map (dgUniverseLiftFunctor.{u, v, w, w, v} F) ≫
        (dgNerveUniverseLiftIso.{u, w, v} A E).inv := by
  calc
    _ = (dgNerveUniverseMap F ≫ (dgNerveUniverseLiftIso.{u, w, v} A E).hom) ≫
        (dgNerveUniverseLiftIso.{u, w, v} A E).inv := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = _ := by rw [dgNerveUniverseMap_lift, Category.assoc]

/-- Hom 複体同型な dg 関手の共通宇宙での nerve は充満忠実。 -/
lemma dgNerveUniverseMap_isFullyFaithful_of_homIso (F : DGFunctor A D E)
    (hi : ∀ x y, IsIso (F.map x y)) : IsFullyFaithful (dgNerveUniverseMap F) := by
  have hF : IsFullyFaithful (dgNerve.map (dgUniverseLiftFunctor.{u, v, w, w, v} F)) :=
    dgNerve_map_isFullyFaithful_of_homIso _ (fun x y => hi x.label.down y.label.down)
  rw [dgNerveUniverseMap_factor]
  have hD := (qCatEquivalenceOfIso
    (dgNerveUniverseLiftIso.{u, v, w} A D)).isQCatEquivalence.isFullyFaithful
  have hE := (qCatEquivalenceOfIso
    (dgNerveUniverseLiftIso.{u, w, v} A E).symm).isQCatEquivalence.isFullyFaithful
  exact hD.comp (hF.comp hE)

end SerrePositivity.InfinityCategories
