module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEndpointMaps
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # ホモトピー円柱の指定両端の単射

概要：任意のパラメータの円柱の両端の和は単射。
方針：各次数で、同じ端では第一射影、異なる端では区間の頂点で区別する。
規約：空パラメータも含む。使われ方：両端固定の有限係数ホモトピー下降。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory SSet
open scoped _root_.Simplicial

/-- ホモトピー円柱の零端・一端をまとめた境界写像。 -/
def homotopyEndpointPair (K : SSet.{u}) : K ⨿ K ⟶ K ⊗ (Δ[1] : SSet.{u}) :=
  coprod.desc SSet.ι₀ SSet.ι₁

private def endpointCoproductIso (K : SSet.{u}) : K ⨿ K ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram K K where
  hom := coprod.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl K K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr K K)
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc coprod.inl coprod.inr
  hom_inv_id := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc]
      rfl
    · rw [← Category.assoc, coprod.inr_desc]
      rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    cases a with
    | inl a =>
      exact congrArg (fun f => f.app n a)
        (coprod.inl_desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl K K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr K K))
    | inr a =>
      exact congrArg (fun f => f.app n a)
        (coprod.inr_desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl K K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr K K))

private def explicitEndpointPair (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram K K ⟶ K ⊗ (Δ[1] : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc SSet.ι₀ SSet.ι₁

private instance explicitEndpointPair_mono (K : SSet.{u}) : Mono (explicitEndpointPair K) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (congrArg Prod.fst h)
    | inr y =>
      have ht := congrArg (fun z => z.2 0) h
      change (0 : Fin 2) = 1 at ht
      exact False.elim (by cases ht)
  | inr x =>
    cases y with
    | inl y =>
      have ht := congrArg (fun z => z.2 0) h
      change (1 : Fin 2) = 0 at ht
      exact False.elim (by cases ht)
    | inr y => exact congrArg Sum.inr (congrArg Prod.fst h)

/-- ホモトピー円柱の両端を合わせた境界写像は単射。 -/
instance homotopyEndpointPair_mono (K : SSet.{u}) : Mono (homotopyEndpointPair K) := by
  have he : (endpointCoproductIso K).hom ≫ explicitEndpointPair K = homotopyEndpointPair K := by
    apply coprod.hom_ext
    · rw [← Category.assoc, endpointCoproductIso, coprod.inl_desc,
        homotopyEndpointPair, coprod.inl_desc]
      rfl
    · rw [← Category.assoc, endpointCoproductIso, coprod.inr_desc,
        homotopyEndpointPair, coprod.inr_desc]
      rfl
  have h : Mono ((endpointCoproductIso K).hom ≫ explicitEndpointPair K) := inferInstance
  rw [he] at h
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
