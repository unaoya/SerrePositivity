module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.CosliceShapeIso

/-!
概要：固定始域の coslice 内の相対余錐を、元の圏の展開図式の余錐と比較する。
方針：既存の反復 coslice 同型と形状同型の制限を合成する。
規約：元の可変図式と全高次成分を保持する。
使われ方：固定始域内の相対因子化を Ind 内の実証済み因子化へ帰着する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
open HomotopyLimits

/-- 概要：固定始域上の余錐圏は、形状を移した全展開図式の余錐圏と厳密に同型。
方針：反復 coslice 同型の後で固定形状の同型に沿って制限する。
規約：元の全単体を保持する実際の同型。
使われ方：固定始域の下での相対因子化。 -/
def fixedSourceUncurryIso {K L M C : SSet.{u}} {p : K ⟶ C}
    (q : L ⟶ sliceUnder p) (e : M ≅ join K L) :
    sliceUnder q ≅ sliceUnder (e.hom ≫ sliceUnderUncurry q) :=
  iteratedSliceUnderIso q ≪≫ cosliceShapeIso e (sliceUnderUncurry q)

/-- 概要：全比較同型の順射は形状同型と再結合による二重展開。
方針：固定形状の制限と既存の反復同型の全族公式を合成する。
規約：任意のパラメーターの全族での等式。
使われ方：余錐と比較辺の同時輸送。 -/
lemma fixedSourceUncurryIso_uncurry {K L M C T : SSet.{u}} {p : K ⟶ C}
    (q : L ⟶ sliceUnder p) (e : M ≅ join K L) (s : T ⟶ sliceUnder q) :
    sliceUnderUncurry (s ≫ (fixedSourceUncurryIso q e).hom) =
      joinMap e.hom (𝟙 T) ≫ (joinAssociator K L T).hom ≫
        sliceUnderUncurry (sliceUnderUncurry s) := by
  simp only [fixedSourceUncurryIso, Iso.trans_hom, cosliceShapeIso]
  rw [← Category.assoc, sliceUnderUncurry_restrict]
  change joinMap e.hom (𝟙 T) ≫ sliceUnderUncurry (s ≫ iteratedSliceUnderMap q) = _
  rw [← iteratedSliceUnderForwardFamily_eq, iteratedSliceUnderForwardFamily_uncurry]

/-- 概要：反復 coslice の全展開は元の前置図式への制限と可換。
方針：二重 uncurry の前合成公式と join の再結合の自然性を使う。
規約：全前置図式の全高次成分を保持する。
使われ方：固定始域内での相対因子化の境界条件。 -/
lemma iteratedSourceUncurry_prefix {K L L' C T : SSet.{u}} {p : K ⟶ C}
    (q : L ⟶ sliceUnder p) (i : L' ⟶ L) (s : T ⟶ sliceUnder q) :
    sliceUnderUncurry (iteratedSliceUnderForwardFamily (i ≫ q)
      (s ≫ sliceUnderRestrict q i)) =
      joinMap (joinMap (𝟙 K) i) (𝟙 T) ≫
        sliceUnderUncurry (iteratedSliceUnderForwardFamily q s) := by
  rw [iteratedSliceUnderForwardFamily_uncurry, iteratedSliceUnderForwardFamily_uncurry,
    sliceUnderUncurry_restrict, sliceUnderUncurry_precomp]
  have h := joinAssociator_naturality (𝟙 K) i (𝟙 T)
  simpa only [joinMap_id, Category.assoc] using
    congrArg (fun f ↦ f ≫ sliceUnderUncurry (sliceUnderUncurry s)) h.symm

/-- 概要：全展開の余錐圏同型は元の底への二重射影を保つ。
方針：形状同型の射影公式と既存の反復同型の射影公式を使う。
規約：元の可変終点と全余錐を保持する。
使われ方：Ind 内へ移した同じ全余錐の filtered 余極限性。 -/
lemma fixedSourceUncurryIso_projection {K L M C : SSet.{u}} {p : K ⟶ C}
    (q : L ⟶ sliceUnder p) (e : M ≅ join K L) :
    (fixedSourceUncurryIso q e).hom ≫ sliceUnderProjection (e.hom ≫ sliceUnderUncurry q) =
      sliceUnderProjection q ≫ sliceUnderProjection p := by
  simp only [fixedSourceUncurryIso, Iso.trans_hom, Category.assoc]
  rw [cosliceShapeIso_projection]
  exact iteratedSliceUnderIso_projection q

/-- 概要：全比較同型による各単体の値は元の二重展開の形状制限。
方針：任意の Yoneda 族に全族公式を適用する。
規約：頂点と辺を同じ全次数の式で扱う。
使われ方：相対因子化の比較辺の厳密な境界条件。 -/
lemma fixedSourceUncurryIso_hom_val {K L M C : SSet.{u}} {p : K ⟶ C}
    (q : L ⟶ sliceUnder p) (e : M ≅ join K L) {n : ℕ}
    (σ : (sliceUnder q) _⦋n⦌) :
    ((fixedSourceUncurryIso q e).hom.app (Opposite.op ⦋n⦌) σ).val =
      joinMap e.hom (𝟙 Δ[n]) ≫ (joinAssociator K L Δ[n]).hom ≫
        sliceUnderUncurry σ.val := by
  have h := fixedSourceUncurryIso_uncurry q e (SSet.yonedaEquiv.symm σ)
  rw [SSet.yonedaEquiv_symm_comp, sliceUnderUncurry_yoneda,
    sliceUnderUncurry_yoneda] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
