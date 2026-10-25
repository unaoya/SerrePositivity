module

public import SerrePositivity.InfinityCategories.F2.Presentable.StandardAlternatingExtension
public import SerrePositivity.InfinityCategories.F2.Presentable.SplitCoconeExtensionFaces
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceShapePushout

/-!
概要：標準交互次段の増大余錐の偶数面を、元の戻り辺の全展開で計算する。
方針：偶数面の join 式と反復 coslice の終点面を自然性で合成する。
規約：元の coslice 辺を選び直さず全余錐射を比較する。
使われ方：filtered 表示の元の増大余錐を保つ有限再帰。
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
variable {C : SSet.{u}} {n : ℕ} {F : (Δ[2 * n] : SSet.{u}) ⟶ C}
  {c d : (sliceUnder F) _⦋0⦌}
  {e : (sliceUnder F).Edge c d} {r : (sliceUnder F).Edge d c}

/-- 概要：次段の全偶数増大余錐は、戻り辺を偶数前置図式へ制限して展開したもの。
方針：標準同型で join へ戻し、全終点面と join の自然性を計算する。
規約：結論は余錐全体の厳密な等式。
使われ方：次の元の表示余錐との整合。 -/
lemma standardAlternatingExtensionCocone_even_join_val
    (T : e.CompStruct r (SSet.Edge.id c)) :
    joinMap (joinStdSimplexIso n 0).hom (𝟙 Δ[0]) ≫
      joinMap (SSet.stdSimplex.map (sequentialEvenFace (n + 1))) (𝟙 Δ[0]) ≫
        (standardAlternatingExtensionCocone e T).val =
      (joinAssociator Δ[n] Δ[0] Δ[0]).hom ≫
        joinMap (𝟙 Δ[n]) (joinStdSimplexIso 0 0).hom ≫
          joinMap (SSet.stdSimplex.map (sequentialEvenFace n)) (𝟙 Δ[1]) ≫
            sliceUnderUncurry (SSet.yonedaEquiv.symm r.edge) := by
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp,
    sequentialEvenFace_successor_join,
    ← Category.comp_id (𝟙 (Δ[0] : SSet.{u})), joinMap_comp, Category.assoc,
    standardAlternatingExtensionCocone_join]
  have h := congrArg
    (fun f ↦ joinMap (joinMap (SSet.stdSimplex.map (sequentialEvenFace n)) (𝟙 Δ[0]))
      (𝟙 Δ[0]) ≫ f) (splitCoconeExtension_target_face T)
  rw [← Category.assoc, ← joinMap_comp, ← joinMap_comp, Category.comp_id,
    Category.id_comp, Category.id_comp] at h
  rw [← Category.assoc _ (joinAssociator Δ[2 * n] Δ[0] Δ[0]).hom,
    joinAssociator_naturality, Category.assoc] at h
  change _ = (joinAssociator Δ[n] Δ[0] Δ[0]).hom ≫
    joinMap (SSet.stdSimplex.map (sequentialEvenFace n)) (joinMap (𝟙 Δ[0]) (𝟙 Δ[0])) ≫
      sliceUnderUncurry ((joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm r.edge) at h
  rw [joinMap_id, sliceUnderUncurry_precomp] at h
  rw [h]
  rw [← Category.assoc (joinMap _ _), ← joinMap_comp,
    Category.comp_id, Category.id_comp,
    ← Category.id_comp (SSet.stdSimplex.map (sequentialEvenFace n)),
    ← Category.comp_id (joinStdSimplexIso 0 0).hom, joinMap_comp, Category.assoc]
  simp only [Category.comp_id, Category.id_comp]

end SerrePositivity.InfinityCategories.F2.Presentable
