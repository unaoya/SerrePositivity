module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RelativeHomotopyEdgeClass
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyRetargetValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RelativePrismHomotopyPrecomp
/-! # 相対 prism から元の道を保つ実変形と辺の類を回収する

概要：両端固定の prism 比較から、元の全区間族を持つ実変形と指定変形との辺の類の一致を得る。
方針：境界の二端を評価して両端を回収し、順序を交換して相対二変形を読む。
規約：元 prism の道・両端・全時間を保持する。
使われ方：明示 augmentation prism と指定係数対角辺の比較を主経路へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
lemma dgGluingRelativePrismHomotopy_endpoint {K Z : SSet.{u}} {F G : (Δ[1] : SSet.{u}) ⊗ K ⟶ Z}
    (H : SSet.Homotopy F G) (i : Fin 2)
    (hH : (((boundary 1).ι ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst ((boundary 1 : SSet.{u}) ⊗ K) Δ[1] ≫ ((boundary 1).ι ▷ K) ≫ G) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i K ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst K (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i K ≫ G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  have hs := congrArg (fun q => q.app n a.1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι i K)
  change ((boundary 1).ι ▷ K).app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint i K).app n a.1) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i K).app n a.1 at hs
  have hh := congrArg (fun q => q.app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint i K).app n a.1, a.2)) hH
  change H.h.app n (((boundary 1).ι ▷ K).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint i K).app n a.1), a.2) =
    G.app n (((boundary 1).ι ▷ K).app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint i K).app n a.1)) at hh
  rw [hs] at hh
  exact hh
lemma dgGluingRelativePrismHomotopy_endpoint_eq {K Z : SSet.{u}} {F G : (Δ[1] : SSet.{u}) ⊗ K ⟶ Z}
    (H : SSet.Homotopy F G) (i : Fin 2)
    (hH : (((boundary 1).ι ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst ((boundary 1 : SSet.{u}) ⊗ K) Δ[1] ≫ ((boundary 1).ι ▷ K) ≫ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i K ≫ F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i K ≫ G := by
  have he := congrArg (fun q => (ι₀ : K ⟶ _) ≫ q) (dgGluingRelativePrismHomotopy_endpoint H i hH)
  have hn : (ι₀ : K ⟶ _) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i K ▷ (Δ[1] : SSet.{u})) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i K ≫ (ι₀ : (Δ[1] : SSet.{u}) ⊗ K ⟶ _) := rfl
  rw [← Category.assoc, hn, Category.assoc, H.h₀] at he
  rw [← Category.assoc, ι₀_fst, Category.id_comp] at he
  exact he

def dgGluingHomotopyOfRelativePrism {K Z : SSet.{u}} {f g : K ⟶ Z}
    (r : SSet.Homotopy f g) {F : (Δ[1] : SSet.{u}) ⊗ K ⟶ Z}
    (H : SSet.Homotopy F ((β_ (Δ[1] : SSet.{u}) K).hom ≫ r.h))
    (hH : (((boundary 1).ι ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst ((boundary 1 : SSet.{u}) ⊗ K) Δ[1] ≫ ((boundary 1).ι ▷ K) ≫
        (β_ (Δ[1] : SSet.{u}) K).hom ≫ r.h) : SSet.Homotopy f g where
  h := (β_ K (Δ[1] : SSet.{u})).hom ≫ F
  h₀ := by
    have hs : (ι₀ : K ⟶ _) ≫ (β_ K (Δ[1] : SSet.{u})).hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K := rfl
    have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom = ι₀ := rfl
    rw [← Category.assoc, hs, dgGluingRelativePrismHomotopy_endpoint_eq H 0 hH,
      ← Category.assoc, ht, r.h₀]
    rfl
  h₁ := by
    have hs : (ι₁ : K ⟶ _) ≫ (β_ K (Δ[1] : SSet.{u})).hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K := rfl
    have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom = ι₁ := rfl
    rw [← Category.assoc, hs, dgGluingRelativePrismHomotopy_endpoint_eq H 1 hH,
      ← Category.assoc, ht, r.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property
lemma dgGluingHomotopyOfRelativePrism_homMk_eq {K Z : SSet.{u}} {f g : K ⟶ Z}
    (r : SSet.Homotopy f g) {F : (Δ[1] : SSet.{u}) ⊗ K ⟶ Z}
    (H : SSet.Homotopy F ((β_ (Δ[1] : SSet.{u}) K).hom ≫ r.h))
    (hH : (((boundary 1).ι ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst ((boundary 1 : SSet.{u}) ⊗ K) Δ[1] ≫ ((boundary 1).ι ▷ K) ≫
        (β_ (Δ[1] : SSet.{u}) K).hom ≫ r.h) :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgGluingHomotopyOfRelativePrism r H hH)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) := by
  have ht : (β_ K (Δ[1] : SSet.{u})).hom ≫
      ((β_ (Δ[1] : SSet.{u}) K).hom ≫ r.h) = r.h := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  let N := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (β_ K (Δ[1] : SSet.{u})).hom) rfl ht
  have hN : N.h = ((β_ K (Δ[1] : SSet.{u})).hom ▷ Δ[1]) ≫ H.h := rfl
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRelativeHomotopy_homMk_eq (dgGluingHomotopyOfRelativePrism r H hH) r N
  · have hs : (ι₀ : K ⟶ _) ≫ (β_ K (Δ[1] : SSet.{u})).hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K := rfl
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom = ι₀ := rfl
    rw [hN, ← Category.assoc, ← comp_whiskerRight, hs,
      dgGluingRelativePrismHomotopy_endpoint H 0 hH]
    rw [reassoc_of% he, r.h₀]
  · have hs : (ι₁ : K ⟶ _) ≫ (β_ K (Δ[1] : SSet.{u})).hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K := rfl
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom = ι₁ := rfl
    rw [hN, ← Category.assoc, ← comp_whiskerRight, hs,
      dgGluingRelativePrismHomotopy_endpoint H 1 hH]
    rw [reassoc_of% he, r.h₁]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
