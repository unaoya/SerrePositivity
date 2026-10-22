module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCocone
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCornerImage

/-!
概要：補間余錐の比較の切断と終点の計算。
方針：結合同型の切断公式と右因子の自然性を使う。
規約：空次数も含む切断表示。使われ方：全円柱比較の逆の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 二重余錐を潰した単体の切断は、元の内側の切断そのもの。 -/
lemma arrowInterpolationConeFold_cut {A : SSet.{u}} {n : ℕ}
    (s : Join.Simplex (join A (Δ[0] : SSet.{u})) Δ[0] n) :
    ((arrowInterpolationConeFold A).app (Opposite.op ⦋n⦌) s).1.val =
      (stableAugJoinEquiv A Δ[0] s.1.val s.2.1).1.val := by
  change (stableAugJoinEquiv A (join Δ[0] Δ[0]) (n + 1)
    (stableAugJoinAssociatorEquiv A Δ[0] Δ[0] (n + 1) s)).1.val = _
  change (stableAugJoinEquiv A (join Δ[0] Δ[0]) (n + 1)
    ((stableAugJoinEquiv A (join Δ[0] Δ[0]) (n + 1)).symm
      (stableAugReassociationEquiv A Δ[0] Δ[0] (n + 1)
        (stableAugJoinEquiv (join A Δ[0]) Δ[0] (n + 1) s)))).1.val = _
  rw [Equiv.apply_symm_apply]
  exact stableAugReassociation_cut A Δ[0] Δ[0] (n + 1) s

/-- 折り畳みの最後の点は、元の余錐の同じ頂点。 -/
lemma arrowInterpolationConeFold_inr (A : SSet.{u}) :
    joinInr (join A (Δ[0] : SSet.{u})) Δ[0] ≫
      arrowInterpolationConeFold A = joinInr A Δ[0] := by
  rw [arrowInterpolationConeFold, ← Category.assoc, stableJoinAssociator_inr,
    Category.assoc, joinInr_joinMap, ← Category.assoc]
  have he : joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ stableLastJoinEvaluation 0 = 𝟙 Δ[0] :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he, Category.id_comp]

/-- 区間の右余錐の最後の点は区間の終点。 -/
lemma arrowInterpolationInterval_inr :
    joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ stableLastJoinEvaluation 1 =
      SSet.const (stdSimplex.obj₀Equiv.symm 1) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  exact stableLastJoinEvaluation_app_of_ge 1 n (Join.Simplex.inr s) i (Nat.zero_le _)

/-- 比較余錐の頂点は、全円柱の新しい終端頂点そのもの。 -/
lemma arrowInterpolationCocone_inr (A : SSet.{u}) :
    joinInr (arrowInterpolationCorner A) (Δ[0] : SSet.{u}) ≫
      arrowInterpolationCocone A = joinInr A Δ[0] ≫ SSet.ι₁ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [arrowInterpolationCocone, Category.assoc, lift_fst, SSet.ι₁_fst,
      Category.comp_id]
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp,
      arrowInterpolationConeFold_inr]
  · simp only [arrowInterpolationCocone, Category.assoc, lift_snd, SSet.ι₁_snd]
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp, arrowInterpolationInterval_inr]
    exact (SSet.comp_const _ _).symm

end SerrePositivity.InfinityCategories.F2.Ind
