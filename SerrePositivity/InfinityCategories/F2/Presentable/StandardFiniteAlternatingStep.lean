module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteStageSuccessor
public import SerrePositivity.InfinityCategories.F2.Presentable.StandardAlternatingExtension
public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteAlternatingSplit

/-!
概要：全交互段の標準拡張の偶数面を、元の小さい表示添字の後続段に同定する。
方針：正規化した coslice 制限の実頂点等式を全余錐値へ戻す。
規約：小さい添字・元の全前置図式・選んだ後続余錐を保持する。
使われ方：fiber の可算交互再帰の偶数段の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：次の全交互図式の偶数面は元の小さい後続表示図式そのもの。
方針：次段の偶数面公式と有限前置 coslice の宇宙比較を合成する。
規約：任意の標的 B への全図式射の等式。
使われ方：交互図式を元の表示添字上の可算図式へ接続する。 -/
lemma standardAlternatingExtension_even_presentation
    {I : SSet.{u}} {B : SSet.{u + 1}} {n : ℕ}
    (a : (Δ[n] : SSet.{u}) ⟶ I)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
    (F : (Δ[2 * n] : SSet.{u + 1}) ⟶ B)
    (heven : SSet.stdSimplex.map (sequentialEvenFace n) ≫ F = finiteStageBaseMap a ≫ D)
    {c d : (sliceUnder F) _⦋0⦌} (e : (sliceUnder F).Edge c d)
    (j : (sliceUnder a) _⦋0⦌)
    (hd : (normalizedCoconeRestriction F (SSet.stdSimplex.map (sequentialEvenFace n)) heven).app
      (Opposite.op ⦋0⦌) d =
      ((finiteStageSourceCosliceIso a).hom ≫ sliceUnderPostcomp (finiteStageBaseMap a) D).app
        (Opposite.op ⦋0⦌) (ULift.up j)) :
    SSet.stdSimplex.map (sequentialEvenFace (n + 1)) ≫ standardAlternatingExtension e =
      finiteStageBaseMap (finiteStageSuccessor j) ≫ D := by
  have h := congrArg Subtype.val hd
  change ((eqToIso (congrArg sliceUnder heven)).hom.app (Opposite.op ⦋0⦌)
    ((sliceUnderRestrict F (SSet.stdSimplex.map (sequentialEvenFace n))).app
      (Opposite.op ⦋0⦌) d)).val = _ at h
  rw [Ind.sliceUnder_eqToIso_val heven] at h
  change joinMap (SSet.stdSimplex.map (sequentialEvenFace n)) (𝟙 Δ[0]) ≫ d.val =
    ((finiteStageSourceCosliceIso a).hom.app (Opposite.op ⦋0⦌) (ULift.up j)).val ≫ D at h
  apply (cancel_epi (joinStdSimplexIso n 0).hom).mp
  rw [standardAlternatingExtension_even, h]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ D) (finiteStageSuccessor_base_join j).symm

end SerrePositivity.InfinityCategories.F2.Presentable
