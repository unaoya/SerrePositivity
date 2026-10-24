module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCoconeMono
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCut

/-!
概要：元の二つの余錐の積を補間領域への余錐と同定する。
方針：最大切断で分解した先頭と余錐点から元の全単体を回収する。
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
/-- 概要：元の二つの余錐の積を補間領域への余錐と同定する。
方針：最大切断で分解した先頭と余錐点から元の全単体を回収する。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
lemma coneTensorCocone_app_surjective (A L : SSet.{u}) (n : ℕ) :
    Function.Surjective ((coneTensorCocone A L).app (Opposite.op ⦋n⦌)) := by
  intro s
  obtain ⟨q, hq⟩ := exists_coneTensor_prefix_lift s
  let r := coneTensorCut s
  have hr : r ≤ n + 1 := coneTensorCut_le s
  let p : Join.augObj (Δ[0] : SSet.{u}) (n + 1 - r) :=
    (Join.stdAugEquiv 0 (n + 1 - r)).symm ⟨fun _ => 0, fun _ _ _ => le_rfl⟩
  let t : Join.Simplex (coneTensorCorner A L) Δ[0] n := ⟨⟨r, by omega⟩, q, p⟩
  refine ⟨t, ?_⟩
  have hp : Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0])
      (Join.prefixIncl (n + 1) r hr) ((coneTensorCocone A L).app (Opposite.op ⦋n⦌) t) =
      Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0])
        (Join.prefixIncl (n + 1) r hr) s :=
    (coneTensorCocone_prefix A L n r hr q p).trans hq
  apply Prod.ext
  · apply coneSimplex_eq_of_prefix hr
    · exact (le_max_left _ _).trans (le_of_eq (coneTensorCocone_cut_max t))
    · exact le_max_left _ _
    · have h := congrArg (Join.augHom (fst (join A (Δ[0] : SSet.{u})) (join L Δ[0])) r) hp
      rw [Join.augHom_naturality, Join.augHom_naturality] at h
      exact h
  · apply coneSimplex_eq_of_prefix hr
    · exact (le_max_right _ _).trans (le_of_eq (coneTensorCocone_cut_max t))
    · exact le_max_right _ _
    · have h := congrArg (Join.augHom (snd (join A (Δ[0] : SSet.{u})) (join L Δ[0])) r) hp
      rw [Join.augHom_naturality, Join.augHom_naturality] at h
      exact h

/-- 概要：元の二つの余錐の積を補間領域への余錐と同定する。
方針：最大切断で分解した先頭と余錐点から元の全単体を回収する。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
instance coneTensorCocone_isIso (A L : SSet.{u}) : IsIso (coneTensorCocone A L) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  rintro ⟨⟨n⟩⟩
  exact (isIso_iff_bijective _).mpr
    ⟨coneTensorCocone_app_injective A L n, coneTensorCocone_app_surjective A L n⟩
/-- 概要：元の二つの余錐の積を補間領域への余錐と同定する。
方針：最大切断で分解した先頭と余錐点から元の全単体を回収する。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
noncomputable def coneTensorCoconeIso (A L : SSet.{u}) :
    join (coneTensorCorner A L) (Δ[0] : SSet.{u}) ≅ join A Δ[0] ⊗ join L Δ[0] :=
  asIso (coneTensorCocone A L)

end SerrePositivity.InfinityCategories.F2.Ind
