module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ArrowIdentityComposition

/-! # 定義展開を抑えた対象の等式に沿う輸送

概要：eqToHom と一致する輸送射を選び、対象の大きな表示を展開せず合成を計算する。
方針：存在証明から射を選択し、eqToHom との等式を公開する。
規約：任意の圏。新しい輸送の公理は加えない。使われ方：D7 の四角形比較の中央の輸送。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory
variable {C : Type*} [Category C]
/-- 通常の eqToHom と一致し、等式の消去を定義展開に要求しない輸送射。 -/
def chosenEqToHom {X Y : C} (h : X = Y) : X ⟶ Y :=
  Classical.choose (show ∃ f : X ⟶ Y, f = eqToHom h from ⟨eqToHom h, rfl⟩)
/-- 選択した輸送射は通常の eqToHom。 -/
lemma chosenEqToHom_eq {X Y : C} (h : X = Y) : chosenEqToHom h = eqToHom h :=
  Classical.choose_spec (show ∃ f : X ⟶ Y, f = eqToHom h from ⟨eqToHom h, rfl⟩)

/-- 輸送射の像を左に合成しても Arrow は変わらない。 -/
lemma arrowMk_map_chosenEqToHom_comp {D : Type*} [Category D] (F : C ⥤ D)
    {X Y Z : C} (h : X = Y) (g : Y ⟶ Z) :
    Arrow.mk (F.map (chosenEqToHom h) ≫ F.map g) = Arrow.mk (F.map g) := by
  rw [chosenEqToHom_eq]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_eqToHom_comp F h g

/-- 輸送射の像を右に合成しても Arrow は変わらない。 -/
lemma arrowMk_map_comp_chosenEqToHom {D : Type*} [Category D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Y) (h : Y = Z) :
    Arrow.mk (F.map f ≫ F.map (chosenEqToHom h)) = Arrow.mk (F.map f) := by
  rw [chosenEqToHom_eq]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_comp_eqToHom F f h
/-- 輸送を挟む合成で左の恒等成分を消す。 -/
lemma arrowMk_map_chosenTransport_comp_of_left_identity {D : Type*} [Category D] (F : C ⥤ D)
    {A B C' E : C} (f : A ⟶ B) (h : B = C') (g : C' ⟶ E) {W : D}
    (hf : Arrow.mk (F.map f) = Arrow.mk (𝟙 W)) :
    Arrow.mk (F.map (f ≫ chosenEqToHom h ≫ g)) = Arrow.mk (F.map g) := by
  rw [chosenEqToHom_eq]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_transport_comp_of_left_identity F f h g hf
/-- 輸送を挟む合成で右の恒等成分を消す。 -/
lemma arrowMk_map_chosenTransport_comp_of_right_identity {D : Type*} [Category D] (F : C ⥤ D)
    {A B C' E : C} (f : A ⟶ B) (h : B = C') (g : C' ⟶ E) {W : D}
    (hg : Arrow.mk (F.map g) = Arrow.mk (𝟙 W)) :
    Arrow.mk (F.map (f ≫ chosenEqToHom h ≫ g)) = Arrow.mk (F.map f) := by
  rw [chosenEqToHom_eq]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_transport_comp_of_right_identity F f h g hg
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
