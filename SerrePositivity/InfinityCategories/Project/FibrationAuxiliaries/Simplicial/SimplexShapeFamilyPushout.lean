module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexChainShape
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
概要：作用素の列で添字付けた単体の依存和は、各係数の pushout を保つ。
方針：各添字で pushout の普遍射を使い、その依存和で普遍射を定める。
規約：単射性は仮定せず、任意の写像による貼り合わせを扱う。
使われ方：底の pushout を実際の単体圏の nerve の pushout へ写す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 添字を保った係数の写像を、その依存和の実際の写像にする。 -/
def simplexShapeFamilyMap {I : Type v} {A B : I → Type (max u v)}
    (f : ∀ t, A t ⟶ B t) : (Σ t, A t) ⟶ Σ t, B t :=
  ↾fun s ↦ ⟨s.1, f s.1 s.2⟩

/-- 各係数の写像が単射なら、添字を保つ依存和の写像も単射。 -/
instance simplexShapeFamilyMap_mono {I : Type v} {A B : I → Type (max u v)}
    (f : ∀ t, A t ⟶ B t) [∀ t, Mono (f t)] : Mono (simplexShapeFamilyMap f) := by
  rw [mono_iff_injective]
  rintro ⟨t, a⟩ ⟨s, b⟩ h
  have ht : t = s := congrArg Sigma.fst h
  subst s
  apply congrArg (Sigma.mk t)
  apply (mono_iff_injective (f t)).mp inferInstance
  exact eq_of_heq (Sigma.mk.inj h).2

/-- 添字ごとに成立する pushout は、依存和全体でも実際の pushout。 -/
lemma simplexShapeFamily_isPushout {I : Type v} {A B C D : I → Type (max u v)}
    {i : ∀ t, A t ⟶ B t} {g : ∀ t, A t ⟶ C t}
    {k : ∀ t, B t ⟶ D t} {j : ∀ t, C t ⟶ D t}
    (h : ∀ t, IsPushout (i t) (g t) (k t) (j t)) :
    IsPushout (simplexShapeFamilyMap i) (simplexShapeFamilyMap g)
      (simplexShapeFamilyMap k) (simplexShapeFamilyMap j) := by
  have hw : simplexShapeFamilyMap i ≫ simplexShapeFamilyMap k =
      simplexShapeFamilyMap g ≫ simplexShapeFamilyMap j := by
    apply ConcreteCategory.hom_ext
    rintro ⟨t, a⟩
    exact congrArg (Sigma.mk t) (ConcreteCategory.congr_hom (h t).w a)
  refine ⟨⟨hw⟩, ⟨?_⟩⟩
  let left (s : PushoutCocone (simplexShapeFamilyMap i) (simplexShapeFamilyMap g))
      (t : I) : B t ⟶ s.pt := ↾fun b ↦ s.inl ⟨t, b⟩
  let right (s : PushoutCocone (simplexShapeFamilyMap i) (simplexShapeFamilyMap g))
      (t : I) : C t ⟶ s.pt := ↾fun c ↦ s.inr ⟨t, c⟩
  have hc (s : PushoutCocone (simplexShapeFamilyMap i) (simplexShapeFamilyMap g))
      (t : I) : i t ≫ left s t = g t ≫ right s t := by
    ext a
    exact ConcreteCategory.congr_hom s.condition ⟨t, a⟩
  refine PushoutCocone.IsColimit.mk hw
    (fun s ↦ ↾fun d ↦ (h d.1).desc (left s d.1) (right s d.1) (hc s d.1) d.2) ?_ ?_ ?_
  · intro s
    ext ⟨t, b⟩
    exact ConcreteCategory.congr_hom ((h t).inl_desc (left s t) (right s t) (hc s t)) b
  · intro s
    ext ⟨t, c⟩
    exact ConcreteCategory.congr_hom ((h t).inr_desc (left s t) (right s t) (hc s t)) c
  · intro s m hm hn
    ext ⟨t, d⟩
    have he : (↾fun d : D t ↦ m ⟨t, d⟩) =
        (h t).desc (left s t) (right s t) (hc s t) := by
      apply (h t).hom_ext
      · ext b
        exact (ConcreteCategory.congr_hom hm ⟨t, b⟩).trans
          (ConcreteCategory.congr_hom ((h t).inl_desc (left s t) (right s t) (hc s t)) b).symm
      · ext c
        exact (ConcreteCategory.congr_hom hn ⟨t, c⟩).trans
          (ConcreteCategory.congr_hom ((h t).inr_desc (left s t) (right s t) (hc s t)) c).symm
    exact ConcreteCategory.congr_hom he d

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
