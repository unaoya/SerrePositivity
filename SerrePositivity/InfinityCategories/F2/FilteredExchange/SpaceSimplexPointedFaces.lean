module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedAugmentation

/-!
概要：一点を前置した実 Space 単体の、初点を保持する全ての面を計算する。
方針：面の順序写像を prepend と同定し、元の head 置換の自然性を適用する。
規約：係数の始域だけを制限し、その標的である元の初点の Hom は変更しない。
使われ方：同じ四面体の三つの pointed 面と指定比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 初点を前置した面写像は、一つ後の頂点を除く元の面写像に等しい。 -/
lemma prependOrderHom_delta {n : ℕ} (i : Fin (n + 2)) :
    prependOrderHom (SimplexCategory.δ i).toOrderHom =
      (SimplexCategory.δ i.succ).toOrderHom := by
  apply DFunLike.ext
  intro j
  induction j using Fin.cases with
  | zero =>
    change (0 : Fin (n + 3)) = i.succ.succAbove 0
    simp
  | succ j =>
    change (i.succAbove j).succ = i.succ.succAbove j.succ
    exact (Fin.succ_succAbove_succ i j).symm

/-- pointed 面は元の係数の同じ面であり、係数の Hom 標的を取り替えない。 -/
lemma spaceSimplexPointedAugmentation_face {n : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌)
    (p : (Δ[n + 1] : SSet.{u}) ⟶ (SimplicialCategory.sHom pointKanObject
      (s.obj ⟨ULift.up 0⟩)).op) (i : Fin (n + 2)) :
    SpaceInfinity.δ i.succ (spaceSimplexPointedAugmentation s p) =
      coneInitialSimplex pointKanObject
        (SpaceInfinity.δ i.succ (coherentConeTailExtension s))
        (stdSimplex.δ i ≫ p) := by
  have h := coneInitialSimplex_reindex pointKanObject (SimplexCategory.δ i)
    (coherentConeTailExtension s) p
  have hl := congrArg (fun α : Fin (n + 2) →o Fin (n + 3) =>
    (SimplicialThickening.functor α.uliftMap).comp SSet
      (spaceSimplexPointedAugmentation s p)) (prependOrderHom_delta i)
  apply hl.symm.trans
  apply h.trans
  congr 1
  exact congrArg (fun α : Fin (n + 2) →o Fin (n + 3) =>
    (SimplicialThickening.functor α.uliftMap).comp SSet
      (coherentConeTailExtension s)) (prependOrderHom_delta i)

/-- 元の初点を残す正の面では、退化 tail の制限は元の面の退化 tail。 -/
lemma coherentConeTailExtension_positive_face {n : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌) (i : Fin (n + 1)) :
    SpaceInfinity.δ i.succ.succ (coherentConeTailExtension s) =
      coherentConeTailExtension (SpaceInfinity.δ i.succ s) := by
  rw [coherentConeTailExtension_eq_sigmaZero, coherentConeTailExtension_eq_sigmaZero]
  exact SSet.δ_comp_σ_of_gt_apply (j := 0) (i := i.succ) (by simp) s

/-- 元の初点を残す pointed 面は、同じ Hom 係数を制限した元の面の実拡張。 -/
lemma spaceSimplexPointedAugmentation_positive_face {n : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌)
    (p : (Δ[n + 1] : SSet.{u}) ⟶ (SimplicialCategory.sHom pointKanObject
      (s.obj ⟨ULift.up 0⟩)).op) (i : Fin (n + 1)) :
    SpaceInfinity.δ i.succ.succ (spaceSimplexPointedAugmentation s p) =
      spaceSimplexPointedAugmentation (SpaceInfinity.δ i.succ s)
        (stdSimplex.δ i.succ ≫ p) := by
  rw [spaceSimplexPointedAugmentation_face]
  unfold spaceSimplexPointedAugmentation
  congr 1
  exact coherentConeTailExtension_positive_face s i

end SerrePositivity.InfinityCategories.F2
