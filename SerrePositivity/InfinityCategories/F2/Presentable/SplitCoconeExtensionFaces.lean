module

public import SerrePositivity.InfinityCategories.F2.Presentable.SplitCoconeExtension

/-!
概要：分裂余錐の全二頂点面を、元の coslice の三角形の面に対応させる。
方針：反復 coslice 同型を全 uncurry と join 再結合で計算する。
規約：全余錐射を比較し、頂点や脚の検査だけで代用しない。
使われ方：可算交互構成の新しい偶数制限と固定標的制限。
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

/-- 概要：反復 coslice の頂点の全余錐値は二重 uncurry の再結合。
方針：頂点の Yoneda 表示に全族の比較を適用する。
規約：元の余錐を選び直さない。
使われ方：分裂三角形の各面の全射比較。 -/
lemma iteratedCocone_vertex_val {K L C : SSet.{u}} {p : K ⟶ C}
    (q : L ⟶ sliceUnder p) (z : (sliceUnder q) _⦋0⦌) :
    ((iteratedSliceUnderIso q).hom.app (Opposite.op ⦋0⦌) z).val =
      (joinAssociator K L Δ[0]).hom ≫ sliceUnderUncurry z.val := by
  have h := iteratedSliceUnderForwardFamily_uncurry q (SSet.yonedaEquiv.symm z)
  rw [iteratedSliceUnderForwardFamily_eq, SSet.yonedaEquiv_symm_comp,
    sliceUnderUncurry_yoneda, sliceUnderUncurry_yoneda] at h
  exact h

variable {K C : SSet.{u}} {F : K ⟶ C} {c d : (sliceUnder F) _⦋0⦌}
  {e : (sliceUnder F).Edge c d} {r : (sliceUnder F).Edge d c}

/-- 概要：分裂余錐の新しい終点側の全二頂点面は元の戻り辺の余錐。
方針：全 uncurry と join の自然性で、三角形の終点面を取り出す。
規約：既存の戻り辺 r を厳密に保持する。
使われ方：次の表示段から固定標的への元の表示脚の整合。 -/
lemma splitCoconeExtension_target_face (T : e.CompStruct r (SSet.Edge.id c)) :
    joinMap (joinMap (𝟙 K) (SSet.stdSimplex.δ (0 : Fin 2))) (𝟙 Δ[0]) ≫
      (splitCoconeExtension T).val =
      (joinAssociator K Δ[0] Δ[0]).hom ≫
        sliceUnderUncurry (edgeCosliceVertex r.toTruncated).val := by
  rw [splitCoconeExtension, iteratedCocone_vertex_val, ← Category.assoc,
    joinAssociator_naturality, Category.assoc, ← sliceUnderUncurry_precomp]
  have h := compStructCocone_target_val T
  change joinMap (SSet.stdSimplex.δ (0 : Fin 2)) (𝟙 Δ[0]) ≫
    (compStructCocone T).val = (edgeCosliceVertex r.toTruncated).val at h
  exact congrArg (fun f : join (Δ[0] : SSet.{u}) Δ[0] ⟶ sliceUnder F ↦
    (joinAssociator K Δ[0] Δ[0]).hom ≫ sliceUnderUncurry f) h

/-- 概要：分裂余錐の新しい始点側の全二頂点面は元の余錐の恒等辺。
方針：全 uncurry と join の自然性で、三角形の対角面を取り出す。
規約：増大余錐の恒等長辺を全て保持する。
使われ方：固定標的の部分列を全定値図式へ比較する。 -/
lemma splitCoconeExtension_source_face (T : e.CompStruct r (SSet.Edge.id c)) :
    joinMap (joinMap (𝟙 K) (SSet.stdSimplex.δ (1 : Fin 2))) (𝟙 Δ[0]) ≫
      (splitCoconeExtension T).val =
      (joinAssociator K Δ[0] Δ[0]).hom ≫
        sliceUnderUncurry (edgeCosliceVertex (SSet.Edge.id c).toTruncated).val := by
  rw [splitCoconeExtension, iteratedCocone_vertex_val, ← Category.assoc,
    joinAssociator_naturality, Category.assoc, ← sliceUnderUncurry_precomp]
  have h := compStructCocone_source_val T
  change joinMap (SSet.stdSimplex.δ (1 : Fin 2)) (𝟙 Δ[0]) ≫
    (compStructCocone T).val = (edgeCosliceVertex (SSet.Edge.id c).toTruncated).val at h
  exact congrArg (fun f : join (Δ[0] : SSet.{u}) Δ[0] ⟶ sliceUnder F ↦
    (joinAssociator K Δ[0] Δ[0]).hom ≫ sliceUnderUncurry f) h

end SerrePositivity.InfinityCategories.F2.Presentable
