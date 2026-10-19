module

public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：同じ底を保つ厳密な引き戻し正方形は、固定した頂点の fiber でも引き戻しになる。
方針：全空間での持ち上げを底の定値条件で fiber へ戻し、包含後に一意性を確認する。
規約：充填性を要求しない。使われ方：形状の押し出しによる固定頂点の余錐空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E₀ E₁ E₂ E₃ S : SSet.{u}}
  (p₀ : E₀ ⟶ S) (p₁ : E₁ ⟶ S) (p₂ : E₂ ⟶ S) (p₃ : E₃ ⟶ S)
  (f : E₀ ⟶ E₁) (g : E₀ ⟶ E₂) (h : E₁ ⟶ E₃) (k : E₂ ⟶ E₃)
  (hf : f ≫ p₁ = p₀) (hg : g ≫ p₂ = p₀)
  (hh : h ≫ p₃ = p₁) (hk : k ≫ p₃ = p₂) (hp : IsPullback f g h k) (y : S _⦋0⦌)

include hp in
/-- 底を保つ引き戻し正方形から、固定した頂点の fiber の引き戻し正方形を得る。 -/
lemma vertexFiberMap_isPullback :
    IsPullback (vertexFiberMap p₀ p₁ f hf y) (vertexFiberMap p₀ p₂ g hg y)
      (vertexFiberMap p₁ p₃ h hh y) (vertexFiberMap p₂ p₃ k hk y) := by
  have hw : vertexFiberMap p₀ p₁ f hf y ≫ vertexFiberMap p₁ p₃ h hh y =
      vertexFiberMap p₀ p₂ g hg y ≫ vertexFiberMap p₂ p₃ k hk y := by
    apply vertexFiber_hom_ext p₃ y
    calc
      _ = vertexFiberι p₀ y ≫ (f ≫ h) := by
        rw [Category.assoc, vertexFiberMap_ι, ← Category.assoc, vertexFiberMap_ι, Category.assoc]
      _ = vertexFiberι p₀ y ≫ (g ≫ k) := congrArg (fun a ↦ vertexFiberι p₀ y ≫ a) hp.w
      _ = _ := by
        symm
        rw [Category.assoc, vertexFiberMap_ι, ← Category.assoc, vertexFiberMap_ι, Category.assoc]
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
  apply PullbackCone.isLimitAux'
  intro s
  have hs : (s.fst ≫ vertexFiberι p₁ y) ≫ h = (s.snd ≫ vertexFiberι p₂ y) ≫ k := by
    have he := congrArg (fun a ↦ a ≫ vertexFiberι p₃ y) s.condition
    simpa only [Category.assoc, vertexFiberMap_ι] using he
  let a := hp.lift (s.fst ≫ vertexFiberι p₁ y) (s.snd ≫ vertexFiberι p₂ y) hs
  have ha : a ≫ p₀ = SSet.const y := by
    rw [← hf, ← Category.assoc, hp.lift_fst, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  let l := vertexFiberLift p₀ y a ha
  have hl : l ≫ vertexFiberι p₀ y = a := vertexFiberLift_ι _ _ _ _
  refine ⟨l, ?_, ?_, ?_⟩
  · change l ≫ vertexFiberMap p₀ p₁ f hf y = s.fst
    apply vertexFiber_hom_ext p₁ y
    rw [Category.assoc, vertexFiberMap_ι, ← Category.assoc, hl]
    exact hp.lift_fst _ _ _
  · change l ≫ vertexFiberMap p₀ p₂ g hg y = s.snd
    apply vertexFiber_hom_ext p₂ y
    rw [Category.assoc, vertexFiberMap_ι, ← Category.assoc, hl]
    exact hp.lift_snd _ _ _
  · intro m hm₁ hm₂
    change m ≫ vertexFiberMap p₀ p₁ f hf y = s.fst at hm₁
    change m ≫ vertexFiberMap p₀ p₂ g hg y = s.snd at hm₂
    apply vertexFiber_hom_ext p₀ y
    rw [hl]
    apply hp.hom_ext
    · rw [Category.assoc, ← vertexFiberMap_ι p₀ p₁ f hf y, ← Category.assoc, hm₁]
      exact (hp.lift_fst _ _ _).symm
    · rw [Category.assoc, ← vertexFiberMap_ι p₀ p₂ g hg y, ← Category.assoc, hm₂]
      exact (hp.lift_snd _ _ _).symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
