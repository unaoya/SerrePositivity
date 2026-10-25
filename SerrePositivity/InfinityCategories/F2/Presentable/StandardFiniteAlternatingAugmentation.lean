module

public import SerrePositivity.InfinityCategories.F2.Presentable.StandardFiniteAlternatingStep
public import SerrePositivity.InfinityCategories.F2.Presentable.StandardAlternatingFaces
public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceRestrictedFaces

/-!
概要：全交互次段の増大余錐の偶数制限は、元の表示余錐の後続制限。
方針：元の戻り辺の全制限と相対表示脚の二重 uncurry を合成する。
規約：元の表示余錐の脚と高次成分を厳密に保持する。
使われ方：元の標的上の可算交互再帰の閉包。
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

/-- 概要：次段の全偶数増大余錐は元の指定表示余錐の制限そのもの。
方針：全偶数面と元の表示脚を厳密に同定し、標準 join 同型を相殺する。
規約：脚だけでなく全余錐射の等式。
使われ方：有限交互段の再帰を元の表示の上で閉じる。 -/
lemma standardAlternatingExtensionCocone_even_presentation
    {I : SSet.{u}} {B : SSet.{u + 1}} {n : ℕ}
    (a : (Δ[n] : SSet.{u}) ⟶ I)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B) (c : JoinCocone D)
    (F : (Δ[2 * n] : SSet.{u + 1}) ⟶ B)
    (heven : SSet.stdSimplex.map (sequentialEvenFace n) ≫ F = finiteStageBaseMap a ≫ D)
    {cF dF : (sliceUnder F) _⦋0⦌}
    {e : (sliceUnder F).Edge cF dF} {r : (sliceUnder F).Edge dF cF}
    (T : e.CompStruct r (SSet.Edge.id cF)) (j : (sliceUnder a) _⦋0⦌)
    (hr : (normalizedCoconeRestriction F (SSet.stdSimplex.map (sequentialEvenFace n)) heven).app
      (Opposite.op ⦋1⦌) r.edge =
      (Compact.coconeTransportLeg (sourceCosliceRestrictedCocone (finiteStageBaseMap a)
        (finiteStageSourceCosliceIso a).hom D c) (ULift.up j)).edge) :
    joinMap (SSet.stdSimplex.map (sequentialEvenFace (n + 1))) (𝟙 Δ[0]) ≫
      (standardAlternatingExtensionCocone e T).val =
      (c.restrict (finiteStageBaseMap (finiteStageSuccessor j))).val := by
  have hU : joinMap (SSet.stdSimplex.map (sequentialEvenFace n)) (𝟙 Δ[1]) ≫
      sliceUnderUncurry (SSet.yonedaEquiv.symm r.edge) =
      sliceUnderUncurry (SSet.yonedaEquiv.symm
        (Compact.coconeTransportLeg (sourceCosliceRestrictedCocone (finiteStageBaseMap a)
          (finiteStageSourceCosliceIso a).hom D c) (ULift.up j)).edge) := by
    rw [← normalizedCoconeRestriction_uncurry F _ heven,
      SSet.yonedaEquiv_symm_comp, hr]
  apply (cancel_epi (joinMap (joinStdSimplexIso n 0).hom (𝟙 (Δ[0] : SSet.{u + 1})))).mp
  rw [standardAlternatingExtensionCocone_even_join_val, hU,
    sourceCosliceRestrictedCocone_leg_uncurry]
  change _ = joinMap (joinStdSimplexIso n 0).hom (𝟙 Δ[0]) ≫
    (joinMap (finiteStageBaseMap (finiteStageSuccessor j)) (𝟙 Δ[0]) ≫ c.val)
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp, finiteStageSuccessor_base_join]

end SerrePositivity.InfinityCategories.F2.Presentable
