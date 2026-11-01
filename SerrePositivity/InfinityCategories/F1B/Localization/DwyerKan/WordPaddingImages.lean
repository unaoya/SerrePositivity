module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordPadding

/-!
# 両端の語を固定した列追加による像の交わりの保存

概要：両端を固定した元の列追加関手は、元の列の像の交わりを保つ。
方針：左端・中央・右端の列に分け、連結写像の像の特徴付けを使う。
規約：両端の全列を共有する同じ元の関手の写像を比較する。
使われ方：padding で前合成した図式の proper 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

lemma sandwichMap_intersection_range (p q : Word) {a b c : Word} (f : a ⟶ c) (g : b ⟶ c) :
    Set.range ((sandwichFunctor p q).map (intersectionInclusion f g)).orderHom =
      Set.range ((sandwichFunctor p q).map f).orderHom ∩
        Set.range ((sandwichFunctor p q).map g).orderHom := by
  change Set.range (appendMap (𝟙 p) (appendMap (intersectionInclusion f g) (𝟙 q))).orderHom =
    Set.range (appendMap (𝟙 p) (appendMap f (𝟙 q))).orderHom ∩
      Set.range (appendMap (𝟙 p) (appendMap g (𝟙 q))).orderHom
  ext j
  cases j using Fin.addCases with
  | left j =>
    simp only [Set.mem_inter_iff]
    erw [appendMap_range_left, appendMap_range_left, appendMap_range_left]
    exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
  | right j =>
    simp only [Set.mem_inter_iff]
    erw [appendMap_range_right, appendMap_range_right, appendMap_range_right]
    cases j using Fin.addCases with
    | left j =>
      erw [appendMap_range_left, appendMap_range_left, appendMap_range_left]
      rw [intersectionInclusion_range]
      rfl
    | right j =>
      erw [appendMap_range_right, appendMap_range_right, appendMap_range_right]
      exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩

end SerrePositivity.EInfinity.Hammock.Word
