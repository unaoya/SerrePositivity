module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCutRecovery
public import SerrePositivity.InfinityCategories.F2.Ind.ConePrefix

/-!
概要：補間領域の右余錐から全円柱への比較は全次数で単射。
方針：像から切断を復元し、先頭制限と元の補間領域の単射性で左因子を回収する。
規約：元の全比較射を使う。使われ方：補間領域の余錐と全円柱の同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 比較後の先頭制限は、元の補間領域の同じ単体を回収する。 -/
lemma arrowInterpolationCocone_prefix (A : SSet.{u}) (n r : ℕ) (hr : r ≤ n + 1)
    (x : Join.augObj (arrowInterpolationCorner A) r)
    (y : Join.augObj (Δ[0] : SSet.{u}) (n + 1 - r)) :
    Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ Δ[1]) (Join.prefixIncl (n + 1) r hr)
      ((arrowInterpolationCocone A).app (Opposite.op ⦋n⦌)
        (⟨⟨r, by omega⟩, x, y⟩ : Join.Simplex (arrowInterpolationCorner A) Δ[0] n)) =
          Join.augHom (arrowInterpolationCornerInclusion A) r x := by
  change Join.augMap _ _ (Join.augHom (arrowInterpolationCocone A) (n + 1) _) = _
  rw [← Join.augHom_naturality, joinSimplex_prefix,
    ← Join.augHom_comp, arrowInterpolationCocone_inl]

/-- 同じ全円柱への比較の各次数の写像は単射。 -/
lemma arrowInterpolationCocone_app_injective (A : SSet.{u}) (n : ℕ) :
    Function.Injective ((arrowInterpolationCocone A).app (Opposite.op ⦋n⦌)) := by
  intro s t h
  have hc : s.1 = t.1 := Fin.ext (Join.cut_ext (n := n + 1)
    (Nat.le_of_lt_succ s.1.isLt) (Nat.le_of_lt_succ t.1.isLt) (by
      intro i
      rw [← arrowInterpolationCocone_vertex_iff s i,
        ← arrowInterpolationCocone_vertex_iff t i, h]))
  rcases s with ⟨ℓ, x, y⟩
  rcases t with ⟨ℓ', x', y'⟩
  dsimp only at hc
  subst ℓ'
  refine Join.Simplex.ext _ _ rfl ?_ ?_
  · change x = x'
    apply Join.augHom_injective (arrowInterpolationCornerInclusion A) ℓ.val
    have he := congrArg
      (Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ Δ[1])
        (Join.prefixIncl (n + 1) ℓ.val (Nat.le_of_lt_succ ℓ.isLt))) h
    rw [arrowInterpolationCocone_prefix, arrowInterpolationCocone_prefix] at he
    exact he
  · change y = y'
    apply (Join.stdAugEquiv 0 _).injective
    apply DFunLike.ext
    intro i
    exact (by decide : ∀ a b : Fin 1, a = b) _ _

/-- 補間余錐の比較は、元の全円柱の部分図式として単射。 -/
instance arrowInterpolationCocone_mono (A : SSet.{u}) : Mono (arrowInterpolationCocone A) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  exact (mono_iff_injective _).mpr (arrowInterpolationCocone_app_injective A n)

end SerrePositivity.InfinityCategories.F2.Ind
