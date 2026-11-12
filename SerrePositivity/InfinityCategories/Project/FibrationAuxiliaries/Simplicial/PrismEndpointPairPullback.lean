module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeArrowCollage
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEndpointMaps
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：区間と底の積の両端の和は単射で両端の pullback を同時に回収する。
方針：次数ごとの直和を左右に分けて各端点の普遍性を使う。
規約：左右の全空間は異なってよい。
使われ方：指定した二つの表現の境界条件を一つの単射にまとめる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 概要：二つの底の和から区間付き底の両端への射。
方針：左右の標準端点を直和からまとめる。
規約：左は零端、右は一端。
使われ方：指定両端表現を延長する底の単射。 -/
def prismEndpointPair (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram B B ⟶ (Δ[1] : SSet.{u}) ⊗ B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B)

/-- 概要：両端の和から区間付き底への射は単射。
方針：同じ端では底の射影、異なる端では区間の頂点で区別する。
規約：底は空でもよい。
使われ方：境界固定の延長定理の適用条件。 -/
instance prismEndpointPair_mono (B : SSet.{u}) : Mono (prismEndpointPair B) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      exact congrArg Sum.inl (congrArg Prod.snd h)
    | inr y =>
      have ht := congrArg (fun z ↦ z.1 0) h
      change (0 : Fin 2) = 1 at ht
      exact False.elim (by cases ht)
  | inr x =>
    cases y with
    | inl y =>
      have ht := congrArg (fun z ↦ z.1 0) h
      change (1 : Fin 2) = 0 at ht
      exact False.elim (by cases ht)
    | inr y =>
      exact congrArg Sum.inr (congrArg Prod.snd h)

/-- 概要：両端の cartesian 正方形の和も cartesian。
方針：直和の単体を左右に分け各端点の存在と一意性を適用する。
規約：全空間の射影の充填性は不要。
使われ方：collage の境界の全空間を元の二つの全空間の和として扱う。 -/
lemma isPullback_prismEndpointPair {E F R B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (r : R ⟶ (Δ[1] : SSet.{u}) ⊗ B)
    (e₀ : E ⟶ R) (e₁ : F ⟶ R)
    (h₀ : IsPullback e₀ p r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B))
    (h₁ : IsPullback e₁ q r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B)) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc e₀ e₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointMap p q) r (prismEndpointPair B) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro x
    cases x with
    | inl x => exact ConcreteCategory.congr_hom (NatTrans.congr_app h₀.w d) x
    | inr x => exact ConcreteCategory.congr_hom (NatTrans.congr_app h₁.w d) x
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact congrArg Sum.inl
          (Types.ext_of_isPullback (h₀.app d) h.1 (Sum.inl.inj h.2))
      | inr y =>
        have hh := h.2
        change Sum.inl (p.app d x) = (Sum.inr (q.app d y) : B.obj d ⊕ B.obj d) at hh
        cases hh
    | inr x =>
      cases y with
      | inl y =>
        have hh := h.2
        change Sum.inr (q.app d x) = (Sum.inl (p.app d y) : B.obj d ⊕ B.obj d) at hh
        cases hh
      | inr y =>
        exact congrArg Sum.inr
          (Types.ext_of_isPullback (h₁.app d) h.1 (Sum.inr.inj h.2))
  · intro x y h
    cases y with
    | inl y =>
      obtain ⟨a, ha, hb⟩ := Types.exists_of_isPullback (h₀.app d) x y h
      exact ⟨Sum.inl a, ha, congrArg Sum.inl hb⟩
    | inr y =>
      obtain ⟨a, ha, hb⟩ := Types.exists_of_isPullback (h₁.app d) x y h
      exact ⟨Sum.inr a, ha, congrArg Sum.inr hb⟩

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
