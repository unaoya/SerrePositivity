module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCorner

/-!
概要：補間領域に属する全単体の具体的な条件。
方針：pushout の全単体の被覆と、join の切断・区間の零座標を使う。
規約：任意の試験形状を許す。使われ方：全円柱の単体から補間余錐の単体を復元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 余錐の単体が元の形状に属することは、その切断が全頂点を含むことと同値。 -/
lemma coneSimplex_inl_iff {A : SSet.{u}} {n : ℕ}
    (s : (join A (Δ[0] : SSet.{u})) _⦋n⦌) :
    (∃ a, Join.Simplex.inl a = s) ↔ s.1.val = n + 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · rcases s with ⟨⟨ℓ, hℓ⟩, x, y⟩
    intro h
    change ℓ = n + 1 at h
    subst ℓ
    refine ⟨x, Join.Simplex.ext _ _ rfl rfl ?_⟩
    apply (Join.stdAugEquiv 0 _).injective
    apply DFunLike.ext
    intro i
    exact (by decide : ∀ a b : Fin 1, a = b) _ _

/-- 全円柱の単体は、元の円柱側または零端点側にあるときちょうど補間領域に属する。 -/
lemma arrowInterpolationCornerInclusion_range_iff {A : SSet.{u}} {n : ℕ}
    (s : (join A (Δ[0] : SSet.{u}) ⊗ Δ[1]) _⦋n⦌) :
    (∃ q, (arrowInterpolationCornerInclusion A).app (Opposite.op ⦋n⦌) q = s) ↔
      s.1.1.val = n + 1 ∨ ∀ i : Fin (n + 1), s.2 i = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    rcases pushout_simplex_covered (SSet.ι₀ : A ⟶ A ⊗ Δ[1])
      (joinInl A Δ[0]) (Opposite.op ⦋n⦌) q with ⟨b, rfl⟩ | ⟨c, rfl⟩
    · have he := ConcreteCategory.congr_hom
        (NatTrans.congr_app (arrowInterpolationCornerInclusion_old A) (Opposite.op ⦋n⦌)) b
      erw [he]
      exact Or.inl rfl
    · have he := ConcreteCategory.congr_hom
        (NatTrans.congr_app (arrowInterpolationCornerInclusion_source A) (Opposite.op ⦋n⦌)) c
      erw [he]
      exact Or.inr (SSet.ι₀_app_snd_apply c)
  · rintro (h | h)
    · obtain ⟨a, ha⟩ := (coneSimplex_inl_iff s.1).mpr h
      refine ⟨(pushout.inl SSet.ι₀ (joinInl A Δ[0])).app _ (a, s.2), ?_⟩
      change ((pushout.inl SSet.ι₀ (joinInl A Δ[0]) ≫
        arrowInterpolationCornerInclusion A).app (Opposite.op ⦋n⦌)) (a, s.2) = s
      rw [arrowInterpolationCornerInclusion_old]
      exact Prod.ext ha rfl
    · refine ⟨(pushout.inr SSet.ι₀ (joinInl A Δ[0])).app _ s.1, ?_⟩
      change ((pushout.inr SSet.ι₀ (joinInl A Δ[0]) ≫
        arrowInterpolationCornerInclusion A).app (Opposite.op ⦋n⦌)) s.1 = s
      rw [arrowInterpolationCornerInclusion_source]
      exact Prod.ext (SSet.ι₀_app_fst s.1) (by
        apply stdSimplex.ext
        intro i
        exact (SSet.ι₀_app_snd_apply s.1 i).trans (h i).symm)

/-- 補間領域の単体では、余錐点に属する全頂点の区間座標は零。 -/
lemma arrowInterpolationCornerInclusion_vertex {A : SSet.{u}} {n : ℕ}
    (q : (arrowInterpolationCorner A) _⦋n⦌) (i : Fin (n + 1))
    (hi : ((arrowInterpolationCornerInclusion A).app (Opposite.op ⦋n⦌) q).1.1.val ≤ i.val) :
    ((arrowInterpolationCornerInclusion A).app (Opposite.op ⦋n⦌) q).2 i = 0 := by
  rcases (arrowInterpolationCornerInclusion_range_iff _).mp ⟨q, rfl⟩ with h | h
  · have := i.isLt
    omega
  · exact h i

end SerrePositivity.InfinityCategories.F2.Ind
