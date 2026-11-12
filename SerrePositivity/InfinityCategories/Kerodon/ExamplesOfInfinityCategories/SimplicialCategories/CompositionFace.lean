module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Path
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathFaces

/-!
# Path の合成面と分割

概要：Path の native な Hom 合成は切断点を通る部分単体集合への同型である。
方針：各 path を切断点の前後へ分割し、和集合が逆になることを証明する。
規約：任意の線形順序で扱い、有限性や追加の充填仮定を用いない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面の貼合せ。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.SimplicialThickening MonoidalCategory

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {J : Type w} [LinearOrder J] {a b c : J}
/-- 概要：切断点を全ての頂点で通る path の列の部分単体集合を定義する。
方針：制限した列でも所属が保たれることを使う。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
def pathThrough (b : J) : (nerve (Path a c)).Subcomplex where
  obj _ := {F | ∀ t, b ∈ (F.obj t).I}
  map f _F h t := h (f.unop.toOrderHom t)
/-- 概要：Mathlib の thickening の native な Hom 合成写像を取る。
方針：単体的豊穣合成 sHomComp を用いる。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
def pathCompMap (a b c : J) : nerve (Path a b) ⊗ nerve (Path b c) ⟶ nerve (Path a c) :=
  SimplicialCategory.sHomComp (SimplicialThickening.mk a)
    (SimplicialThickening.mk b) (SimplicialThickening.mk c)
/-- 概要：二つの path の合成を切断点以下に制限すると前半を回収する。
方針：後半の点が切断点以下なら切断点自身であることを使う。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
lemma pathPrefix_of_comp (p : Path a b) (q : Path b c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathPrefix (@CategoryStruct.comp (SimplicialThickening J) _ (.mk a) (.mk b) (.mk c) p q)
      b (Or.inl p.right) = p := by
  apply Path.ext
  ext x
  change ((x ∈ p.I ∨ x ∈ q.I) ∧ x ≤ b) ↔ x ∈ p.I
  constructor
  · rintro ⟨h | h, hx⟩
    · exact h
    · have he : x = b := le_antisymm hx (q.left_le x h)
      exact he ▸ p.right
  · intro h
    exact ⟨Or.inl h, p.le_right x h⟩
/-- 概要：二つの path の合成を切断点以上に制限すると後半を回収する。
方針：前半の点が切断点以上なら切断点自身であることを使う。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
lemma pathSuffix_of_comp (p : Path a b) (q : Path b c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathSuffix (@CategoryStruct.comp (SimplicialThickening J) _ (.mk a) (.mk b) (.mk c) p q)
      b (Or.inl p.right) = q := by
  apply Path.ext
  ext x
  change ((x ∈ p.I ∨ x ∈ q.I) ∧ b ≤ x) ↔ x ∈ q.I
  constructor
  · rintro ⟨h | h, hx⟩
    · have he : x = b := le_antisymm (p.le_right x h) hx
      exact he ▸ q.left
    · exact h
  · intro h
    exact ⟨Or.inr h, q.left_le x h⟩
/-- 概要：切断点を通る path の列を前半の列へ制限する。
方針：各 path を切断点以下へ制限し、包含も制限する。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
def pathThroughPrefix {n : SimplexCategoryᵒᵖ}
    (F : (pathThrough (a := a) (c := c) b : SSet).obj n) : (nerve (Path a b)).obj n where
  obj t := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathPrefix (F.1.obj t) b (F.2 t)
  map f := ⟨⟨⟨fun x hx ↦ ⟨(F.1.map f).1.1.1 hx.1, hx.2⟩⟩⟩⟩
/-- 概要：切断点を通る path の列を後半の列へ制限する。
方針：各 path を切断点以上へ制限し、包含も制限する。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
def pathThroughSuffix {n : SimplexCategoryᵒᵖ}
    (F : (pathThrough (a := a) (c := c) b : SSet).obj n) : (nerve (Path b c)).obj n where
  obj t := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathSuffix (F.1.obj t) b (F.2 t)
  map f := ⟨⟨⟨fun x hx ↦ ⟨(F.1.map f).1.1.1 hx.1, hx.2⟩⟩⟩⟩
/-- 概要：native な Hom 合成は切断点を通る部分単体集合へ因子分解する。
方針：和集合が切断点を含むことを使う。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
def pathCompToThrough (a b c : J) :
    nerve (Path a b) ⊗ nerve (Path b c) ⟶ pathThrough (a := a) (c := c) b where
  app n := ↾fun z ↦ ⟨(pathCompMap a b c).app n z,
    fun t ↦ Or.inl (z.1.obj t).right⟩
  naturality := by
    intro n m f
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact NatTrans.naturality_apply (pathCompMap a b c) f z

/-- 概要：切断点を通る単体集合を前半と後半の直積へ写す。
方針：prefix と suffix の列を取り、反変作用との可換性を確認する。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
def pathThroughSplit (a b c : J) :
    (pathThrough (a := a) (c := c) b : SSet) ⟶ nerve (Path a b) ⊗ nerve (Path b c) where
  app n := ↾fun F ↦ ⟨pathThroughPrefix F, pathThroughSuffix F⟩
  naturality := by
    intro n m f
    apply ConcreteCategory.hom_ext
    intro F
    apply Prod.ext
    · exact CategoryTheory.Functor.ext (fun _ ↦ rfl)
    · exact CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- 概要：native な二つの Hom の直積は切断点を通る合成面と同型である。
方針：prefix と suffix による分割と和集合による合成が互いに逆であることを使う。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
def pathThroughIso (a b c : J) :
    nerve (Path a b) ⊗ nerve (Path b c) ≅ pathThrough (a := a) (c := c) b where
  hom := pathCompToThrough a b c
  inv := pathThroughSplit a b c
  hom_inv_id := by
    apply CategoryTheory.NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · exact CategoryTheory.Functor.ext (fun t ↦ pathPrefix_of_comp (z.1.obj t) (z.2.obj t))
    · exact CategoryTheory.Functor.ext (fun t ↦ pathSuffix_of_comp (z.1.obj t) (z.2.obj t))
  inv_hom_id := by
    apply CategoryTheory.NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    exact CategoryTheory.Functor.ext
      (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathPrefix_comp_pathSuffix (F.1.obj t) b (F.2 t))
/-- 概要：合成面との同型と包含の合成は native な Hom 合成である。
方針：因子分解の定義を用いる。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
lemma pathThroughIso_hom_ι (a b c : J) :
    (pathThroughIso a b c).hom ≫ (pathThrough (a := a) (c := c) b).ι =
      pathCompMap a b c := rfl
/-- 概要：native な Hom 合成写像は単射である。
方針：合成面への同型と包含へ因子分解する。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
lemma pathCompMap_mono (a b c : J) : Mono (pathCompMap a b c) := by
  rw [← pathThroughIso_hom_ι]
  infer_instance
/-- 概要：native な Hom 合成の像は切断点を通る部分単体集合である。
方針：合成面への同型を使い像を計算する。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
lemma range_pathCompMap (a b c : J) :
    SSet.Subcomplex.range (pathCompMap a b c) = pathThrough (a := a) (c := c) b := by
  rw [← pathThroughIso_hom_ι, SSet.Subcomplex.range_comp,
    SSet.Subcomplex.range_eq_top, SSet.Subcomplex.image_top]
  exact Subfunctor.range_ι _
/-- 概要：零座標面を合成で引き戻すと前半と後半の零座標面の直積になる。
方針：和集合が点を避けることを両部分集合の条件に分解する。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
lemma pathAvoids_preimage_pathCompMap (j a b c : J) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := a) (b := c) j).preimage (pathCompMap a b c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := a) (b := b) j).prod (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := b) (b := c) j) := by
  ext n z
  change (∀ t, j ∉ (z.1.obj t).I ∪ (z.2.obj t).I) ↔
    (∀ t, j ∉ (z.1.obj t).I) ∧ ∀ t, j ∉ (z.2.obj t).I
  simp only [Set.mem_union, not_or, forall_and]
/-- 概要：前の切断点を通る合成面の逆像は前半の合成面と後半全体の直積になる。
方針：後半にある前の切断点は合成の切断点自身になることを使う。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
lemma pathThrough_preimage_pathCompMap_of_le (a b c d : J) (hdb : d ≤ b) :
    (pathThrough (a := a) (c := c) d).preimage (pathCompMap a b c) =
      (pathThrough (a := a) (c := b) d).prod ⊤ := by
  ext n z
  change (∀ t, d ∈ (z.1.obj t).I ∪ (z.2.obj t).I) ↔
    (∀ t, d ∈ (z.1.obj t).I) ∧ True
  constructor
  · intro h
    refine ⟨fun t ↦ ?_, trivial⟩
    rcases h t with h | h
    · exact h
    · have he : d = b := le_antisymm hdb ((z.2.obj t).left_le d h)
      exact he ▸ (z.1.obj t).right
  · rintro ⟨h, _⟩ t
    exact Or.inl (h t)
/-- 概要：後の切断点を通る合成面の逆像は前半全体と後半の合成面の直積になる。
方針：前半にある後の切断点は合成の切断点自身になることを使う。
規約：包含方向の path と和集合の合成を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の合成面とその重なり。 -/
lemma pathThrough_preimage_pathCompMap_of_ge (a b c d : J) (hbd : b ≤ d) :
    (pathThrough (a := a) (c := c) d).preimage (pathCompMap a b c) =
      (⊤ : (nerve (Path a b)).Subcomplex).prod (pathThrough (a := b) (c := c) d) := by
  ext n z
  change (∀ t, d ∈ (z.1.obj t).I ∪ (z.2.obj t).I) ↔
    True ∧ ∀ t, d ∈ (z.2.obj t).I
  constructor
  · intro h
    refine ⟨trivial, fun t ↦ ?_⟩
    rcases h t with h | h
    · have he : d = b := le_antisymm ((z.1.obj t).le_right d h) hbd
      exact he ▸ (z.2.obj t).left
    · exact h
  · rintro ⟨_, h⟩ t
    exact Or.inr (h t)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
