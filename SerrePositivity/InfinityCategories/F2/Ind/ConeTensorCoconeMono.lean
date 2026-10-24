module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCoconeCut
public import SerrePositivity.InfinityCategories.F2.Ind.ConePrefix

/-!
概要：元の補間余錐の比較は全次数で単射。
方針：最大切断を回収し、その先頭制限から元の補間単体を回収する。
規約：任意の元の両形状と全境界を保持し、有限性を要求しない。
使われ方：有限半順序形状の点追加における相対補間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の補間余錐の比較は全次数で単射。
方針：最大切断を回収し、その先頭制限から元の補間単体を回収する。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
lemma coneTensorCocone_prefix (A L : SSet.{u}) (n r : ℕ) (hr : r ≤ n + 1)
    (x : Join.augObj (coneTensorCorner A L) r)
    (y : Join.augObj (Δ[0] : SSet.{u}) (n + 1 - r)) :
    Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0]) (Join.prefixIncl (n + 1) r hr)
      ((coneTensorCocone A L).app (Opposite.op ⦋n⦌)
        (⟨⟨r, by omega⟩, x, y⟩ : Join.Simplex (coneTensorCorner A L) Δ[0] n)) =
          Join.augHom (coneTensorCornerInclusion A L) r x := by
  change Join.augMap _ _ (Join.augHom (coneTensorCocone A L) (n + 1) _) = _
  rw [← Join.augHom_naturality, joinSimplex_prefix,
    ← Join.augHom_comp, coneTensorCocone_inl]
/-- 概要：元の補間余錐の比較は全次数で単射。
方針：最大切断を回収し、その先頭制限から元の補間単体を回収する。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
lemma coneTensorCocone_app_injective (A L : SSet.{u}) (n : ℕ) :
    Function.Injective ((coneTensorCocone A L).app (Opposite.op ⦋n⦌)) := by
  intro s t h
  have hc : s.1 = t.1 := Fin.ext ((coneTensorCocone_cut_max s).symm.trans
    ((congrArg (fun z : (join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0]) _⦋n⦌ ↦
      max z.1.1.val z.2.1.val) h).trans (coneTensorCocone_cut_max t)))
  rcases s with ⟨ℓ, x, y⟩
  rcases t with ⟨ℓ', x', y'⟩
  dsimp only at hc
  subst ℓ'
  refine Join.Simplex.ext _ _ rfl ?_ ?_
  · change x = x'
    apply Join.augHom_injective (coneTensorCornerInclusion A L) ℓ.val
    have he := congrArg
      (Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0])
        (Join.prefixIncl (n + 1) ℓ.val (Nat.le_of_lt_succ ℓ.isLt))) h
    rw [coneTensorCocone_prefix, coneTensorCocone_prefix] at he
    exact he
  · change y = y'
    apply (Join.stdAugEquiv 0 _).injective
    apply DFunLike.ext
    intro i
    exact (by decide : ∀ a b : Fin 1, a = b) _ _

/-- 概要：元の余錐比較は単射。方針：各次数の単射性。
規約：元の全射。使われ方：比較の同型と境界回収。 -/
instance coneTensorCocone_mono (A L : SSet.{u}) : Mono (coneTensorCocone A L) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  exact (mono_iff_injective _).mpr (coneTensorCocone_app_injective A L n)

end SerrePositivity.InfinityCategories.F2.Ind
