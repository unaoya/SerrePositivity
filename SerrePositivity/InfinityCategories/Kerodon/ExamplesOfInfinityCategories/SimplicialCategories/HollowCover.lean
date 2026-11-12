module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathHollow
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionFace
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# 空洞部分の面による被覆

概要：Path の空洞部分は全ての合成面と指定外の零座標面の和である。
方針：増大列の最初と最後の頂点で所属を判定し、部分単体集合の余極限を使う。
規約：内部点を含むことが合成面、欠くことが零座標面を表す。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の既知データの貼合せ。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialThickening

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {J : Type v} [LinearOrder J] {a b : J}

/-- 概要：合成面への所属は最初の path が切断点を含むことと同値である。
方針：列の最初の頂点から各頂点への包含を使う。
規約：Path の射は包含方向。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の空洞部分の合成面の判定。 -/
lemma mem_pathThrough_iff_first (c : J) {m : SimplexCategoryᵒᵖ}
    (F : (nerve (Path a b)).obj m) :
    F ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough c).obj m ↔ c ∈ (F.obj 0).I := by
  change (∀ t, c ∈ (F.obj t).I) ↔ c ∈ (F.obj 0).I
  exact ⟨fun h ↦ h 0, fun h t ↦ (F.map (homOfLE (Fin.zero_le t))).1.1.1 h⟩

/-- 概要：零座標面への所属は最後の path が指定点を欠くことと同値である。
方針：各頂点から最後の頂点への包含を使う。
規約：Path の射は包含方向。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の空洞部分の零座標面の判定。 -/
lemma mem_pathAvoids_iff_last (c : J) {m : SimplexCategoryᵒᵖ}
    (F : (nerve (Path a b)).obj m) :
    F ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids c).obj m ↔ c ∉ (F.obj (Fin.last m.unop.len)).I := by
  change (∀ t, c ∉ (F.obj t).I) ↔ c ∉ (F.obj (Fin.last m.unop.len)).I
  exact ⟨fun h ↦ h _, fun h t ht ↦ h ((F.map (homOfLE (Fin.le_last t))).1.1.1 ht)⟩

/-- 概要：空洞部分を覆う合成面と指定外の零座標面を一つの族にする。
方針：直和の左側に合成面、右側に零座標面を置く。
規約：右側の添字では欠ける零座標面 i を除く。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の面の貼合せの添字。 -/
def pathHollowFace (i : Set.Ioo a b) :
    Sum (Set.Ioo a b) {j : Set.Ioo a b // j ≠ i} → (nerve (Path a b)).Subcomplex
  | .inl c => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough c.1
  | .inr j => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids j.1.1

/-- 概要：面族の和は空洞部分そのものに等しい。
方針：最初と最後の頂点による所属判定を空洞部分の判定と比較する。
規約：任意の線形順序の真の区間で扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の既知部分の正確な被覆。 -/
lemma iSup_pathHollowFace (hab : a < b) (i : Set.Ioo a b) :
    ⨆ j, pathHollowFace i j = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollow hab i := by
  ext m F
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.mem_pathHollow_iff]
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro ⟨j | j, hj⟩
    · exact Or.inl ⟨j, (mem_pathThrough_iff_first j.1 F).mp hj⟩
    · exact Or.inr ⟨j.1, j.2, (mem_pathAvoids_iff_last j.1.1 F).mp hj⟩
  · rintro (⟨j, hj⟩ | ⟨j, hji, hj⟩)
    · exact ⟨.inl j, (mem_pathThrough_iff_first j.1 F).mpr hj⟩
    · exact ⟨.inr ⟨j, hji⟩, (mem_pathAvoids_iff_last j.1 F).mpr hj⟩

/-- 概要：空洞部分と面族、その二つずつの交わりは多重余等化子の図式をなす。
方針：被覆の等式と交わりの定義を使う。
規約：全ての順序付きの面の対を関係として用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） の整合する面上の写像の降下。 -/
theorem pathHollowCover (hab : a < b) (i : Set.Ioo a b) :
    SSet.Subcomplex.MulticoequalizerDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollow hab i) (pathHollowFace i)
      (fun j k ↦ pathHollowFace i j ⊓ pathHollowFace i k) where
  iSup_eq := iSup_pathHollowFace hab i
  eq_inf _ _ := rfl

/-- 概要：各被覆面を空洞部分に含める。
方針：族の一項は和以下であることと被覆の等式を使う。
規約：全ての面に同じ添字型を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） の貼合せ後の制限の計算。 -/
lemma pathHollowFace_le (hab : a < b) (i : Set.Ioo a b)
    (j : Sum (Set.Ioo a b) {j : Set.Ioo a b // j ≠ i}) :
    pathHollowFace i j ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollow hab i := by
  rw [← iSup_pathHollowFace hab i]
  exact le_iSup _ j

/-- 概要：交わりで一致する面上の写像を空洞部分上の写像へ貼り合わせる。
方針：部分単体集合の多重余等化子の普遍性を使う。
規約：一般の貼合せ補題であり、ホーンからの整合性は別途証明する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） のホーンの Hom 写像の構成。 -/
noncomputable def pathHollowGlue (hab : a < b) (i : Set.Ioo a b) {X : SSet.{v}}
    (f : ∀ j, (pathHollowFace i j : SSet) ⟶ X)
    (hf : ∀ j k, SSet.Subcomplex.homOfLE
      (show pathHollowFace i j ⊓ pathHollowFace i k ≤ pathHollowFace i j from inf_le_left) ≫
        f j = SSet.Subcomplex.homOfLE
      (show pathHollowFace i j ⊓ pathHollowFace i k ≤ pathHollowFace i k from inf_le_right) ≫
        f k) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollow hab i : SSet) ⟶ X :=
  Multicofork.IsColimit.desc (pathHollowCover hab i).isColimit f
    (fun ⟨j, k⟩ ↦ hf j k)

/-- 概要：貼合せを各面に制限すると与えた写像に戻る。
方針：多重余等化子の降下の制限則を使う。
規約：面の包含は被覆の不等式から取る。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） のホーンと合成則の回収。 -/
lemma pathHollowGlue_on_face (hab : a < b) (i : Set.Ioo a b) {X : SSet.{v}}
    (f : ∀ j, (pathHollowFace i j : SSet) ⟶ X)
    (hf : ∀ j k, SSet.Subcomplex.homOfLE
      (show pathHollowFace i j ⊓ pathHollowFace i k ≤ pathHollowFace i j from inf_le_left) ≫
        f j = SSet.Subcomplex.homOfLE
      (show pathHollowFace i j ⊓ pathHollowFace i k ≤ pathHollowFace i k from inf_le_right) ≫
        f k)
    (j : Sum (Set.Ioo a b) {j : Set.Ioo a b // j ≠ i}) :
    SSet.Subcomplex.homOfLE (pathHollowFace_le hab i j) ≫ pathHollowGlue hab i f hf =
      f j :=
  Multicofork.IsColimit.fac (pathHollowCover hab i).isColimit f (fun ⟨j, k⟩ ↦ hf j k) j

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
