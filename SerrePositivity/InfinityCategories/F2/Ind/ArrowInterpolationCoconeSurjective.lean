module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowPrismCut
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCoconeMono

/-!
概要：補間領域の右余錐から全円柱への比較は全次数で全射。
方針：最大切断までの補間単体に終端点を加え、先頭制限と終端座標で元の全単体を回収。
規約：元の比較射そのものの全射性。使われ方：全円柱の厳密な形状同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の全円柱の任意の単体は、補間余錐の単体の像。 -/
lemma arrowInterpolationCocone_app_surjective (A : SSet.{u}) (n : ℕ) :
    Function.Surjective ((arrowInterpolationCocone A).app (Opposite.op ⦋n⦌)) := by
  intro s
  obtain ⟨q, hq⟩ := exists_arrowPrism_prefix_lift s
  let r := arrowPrismCut s
  have hr : r ≤ n + 1 := arrowPrismCut_le s
  let p : Join.augObj (Δ[0] : SSet.{u}) (n + 1 - r) :=
    (Join.stdAugEquiv 0 (n + 1 - r)).symm ⟨fun _ => 0, fun _ _ _ => le_rfl⟩
  let t : Join.Simplex (arrowInterpolationCorner A) Δ[0] n := ⟨⟨r, by omega⟩, q, p⟩
  refine ⟨t, ?_⟩
  have hp : Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ Δ[1])
      (Join.prefixIncl (n + 1) r hr)
        ((arrowInterpolationCocone A).app (Opposite.op ⦋n⦌) t) =
      Join.augMap (join A (Δ[0] : SSet.{u}) ⊗ Δ[1])
        (Join.prefixIncl (n + 1) r hr) s :=
    (arrowInterpolationCocone_prefix A n r hr q p).trans hq
  apply Prod.ext
  · apply coneSimplex_eq_of_prefix hr
    · rw [arrowInterpolationCocone_cut]
      exact Nat.le_of_lt_succ (arrowInterpolationAugX A r q).1.isLt
    · exact le_max_left _ _
    · have h := congrArg (Join.augHom (fst (join A (Δ[0] : SSet.{u})) Δ[1]) r) hp
      rw [Join.augHom_naturality, Join.augHom_naturality] at h
      exact h
  · apply stdSimplex.ext
    intro i
    by_cases hi : i.val < r
    · have h := congrArg (fun z => Join.stdAugEquiv 1 r
        (Join.augHom (snd (join A (Δ[0] : SSet.{u})) Δ[1]) r z) ⟨i.val, hi⟩) hp
      rw [Join.augHom_naturality, Join.augHom_naturality,
        Join.stdAugEquiv_augMap, Join.stdAugEquiv_augMap] at h
      exact h
    · have hb : intervalZeroCut s.2 ≤ i.val :=
        (le_max_right _ _).trans (Nat.le_of_not_gt hi)
      exact (arrowInterpolationCocone_y_ge t i (Nat.le_of_not_gt hi)).trans
        (intervalZeroCut_ge s.2 i hb).symm

/-- この元の比較射の全次数の成分は全単射。 -/
lemma arrowInterpolationCocone_app_bijective (A : SSet.{u}) (n : ℕ) :
    Function.Bijective ((arrowInterpolationCocone A).app (Opposite.op ⦋n⦌)) :=
  ⟨arrowInterpolationCocone_app_injective A n, arrowInterpolationCocone_app_surjective A n⟩

/-- 補間領域の右余錐は元の全円柱と厳密に同型。 -/
instance arrowInterpolationCocone_isIso (A : SSet.{u}) : IsIso (arrowInterpolationCocone A) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  rintro ⟨⟨n⟩⟩
  exact (isIso_iff_bijective _).mpr (arrowInterpolationCocone_app_bijective A n)

/-- 全円柱を補間領域の右余錐として表す同型。 -/
def arrowInterpolationCoconeIso (A : SSet.{u}) :
    join (arrowInterpolationCorner A) (Δ[0] : SSet.{u}) ≅ join A Δ[0] ⊗ Δ[1] :=
  asIso (arrowInterpolationCocone A)

end SerrePositivity.InfinityCategories.F2.Ind
