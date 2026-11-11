module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionFace

/-!
# 二つの合成面の交わり

概要：二つの切断点を通る部分単体集合は三つの Hom の合成で覆われる。
方針：後の切断点で分割し、その前半を前の切断点で分割する。
規約：切断点は弱い順序で比較し、端点の内部性は要求しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面どうしの整合性。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.SimplicialThickening MonoidalCategory

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {J : Type v} [LinearOrder J]

/-- 概要：三つの native Hom を左から順に合成する。
方針：最初の二つを合成し、残りの Hom と合成する。
規約：定義域の括弧は左結合とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の二つの合成面の共通データ。 -/
def pathTripleCompMap (a b c d : J) :
    (nerve (Path a b) ⊗ nerve (Path b c)) ⊗ nerve (Path c d) ⟶ nerve (Path a d) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a b c ⊗ₘ 𝟙 (nerve (Path c d))) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a c d

/-- 概要：三重合成の各頂点は両切断点を含む。
方針：和集合に最初の Hom の右端点と最後の Hom の左端点を入れる。
規約：単体の次数と三つの Hom の単体を明示する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の共通部分への因子分解。 -/
lemma pathTripleCompMap_mem (a b c d : J) (m : SimplexCategoryᵒᵖ)
    (z : ((nerve (Path a b) ⊗ nerve (Path b c)) ⊗ nerve (Path c d)).obj m) :
    (pathTripleCompMap a b c d).app m z ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := d) b ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough c).obj m := by
  change (∀ t, b ∈ (((pathTripleCompMap a b c d).app m z).obj t).I) ∧
    ∀ t, c ∈ (((pathTripleCompMap a b c d).app m z).obj t).I
  exact ⟨fun t ↦ Or.inl (Or.inl (z.1.1.obj t).right),
    fun t ↦ Or.inr (z.2.obj t).left⟩

set_option backward.isDefEq.respectTransparency false in
/-- 概要：三つの Hom の合成は両切断点を通る交わりへ因子分解する。
方針：和集合は前半の右端点と最後の左端点を含む。
規約：切断点の比較を仮定しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の共通部分を三つの Hom で検査する。 -/
def pathTripleToIntersection (a b c d : J) :
    (nerve (Path a b) ⊗ nerve (Path b c)) ⊗ nerve (Path c d) ⟶
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := d) b ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough c :
        (nerve (Path a d)).Subcomplex) : SSet) :=
  SSet.Subcomplex.lift (pathTripleCompMap a b c d) (by
    intro m y hy
    obtain ⟨z, rfl⟩ := hy
    exact pathTripleCompMap_mem a b c d m z)

/-- 概要：共通部分への因子分解を周囲に含めると三重合成に戻る。
方針：包含の定義を展開する。
規約：native な合成写像との厳密な等式。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） の重なり上の写像の比較。 -/
lemma pathTripleToIntersection_ι (a b c d : J) :
    pathTripleToIntersection a b c d ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := d) b ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough c).ι =
        pathTripleCompMap a b c d := rfl

/-- 概要：順序付けられた切断点の共通部分は三つの Hom の合成で全射に覆われる。
方針：各単体を後の切断点で分割し、前半を前の切断点で分割して回収する。
規約：切断点の一致も許す。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） の合成面の整合性を結合律へ帰着する。 -/
lemma pathTripleToIntersection_epi (a b c d : J) (hbc : b ≤ c) :
    Epi (pathTripleToIntersection a b c d) := by
  rw [NatTrans.epi_iff_epi_app]
  intro m
  apply (epi_iff_surjective _).mpr
  intro F
  let G : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := d) c : SSet).obj m := ⟨F.1, F.2.2⟩
  let L : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := c) b : SSet).obj m :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughPrefix G, fun t ↦ ⟨F.2.1 t, hbc⟩⟩
  refine ⟨⟨⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughPrefix L, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughSuffix L⟩, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughSuffix G⟩, ?_⟩
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  change @CategoryStruct.comp (SimplicialThickening J) _ (.mk a) (.mk c) (.mk d)
    (@CategoryStruct.comp (SimplicialThickening J) _ (.mk a) (.mk b) (.mk c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathPrefix (L.1.obj t) b (L.2 t)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathSuffix (L.1.obj t) b (L.2 t)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathSuffix (G.1.obj t) c (G.2 t)) = F.1.obj t
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathPrefix_comp_pathSuffix]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathPrefix_comp_pathSuffix (F.1.obj t) c (F.2.2 t)

/-- 概要：共通部分から後の合成面への写像は最初の二つの Hom の合成で表せる。
方針：因子分解と合成面への同型の定義を比較する。
規約：定義域は左結合の三つの Hom の直積。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） の後の切断点での評価。 -/
lemma pathTripleToIntersection_toSecond (a b c d : J) :
    pathTripleToIntersection a b c d ≫ SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := d) b ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough c ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough c
        from inf_le_right) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a b c ⊗ₘ 𝟙 (nerve (Path c d))) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso a c d).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- 概要：共通部分から前の合成面への写像は後ろの二つの Hom の合成で表せる。
方針：周囲への包含を消去し、native な豊穣合成の結合律を使う。
規約：結合子で左結合の直積から右結合の直積へ移す。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） の前の切断点での評価。 -/
lemma pathTripleToIntersection_toFirst (a b c d : J) :
    pathTripleToIntersection a b c d ≫ SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := d) b ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough c ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough b
        from inf_le_left) =
      (α_ (nerve (Path a b)) (nerve (Path b c)) (nerve (Path c d))).hom ≫
        (𝟙 (nerve (Path a b)) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap b c d) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso a b d).hom := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := d) b).ι).mp
  simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso_hom_ι]
  rw [← Category.assoc, pathTripleToIntersection_ι]
  simp only [pathTripleCompMap, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap, tensorHom_id, id_tensorHom,
    Category.assoc]
  convert (e_assoc' SSet (SimplicialThickening.mk a) (SimplicialThickening.mk b)
    (SimplicialThickening.mk c) (SimplicialThickening.mk d)).symm using 1


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
