module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.EqToHom
/-!
# 元の射列の頂点列と隣接 Hom による座標

概要：任意長の元の射列を頂点列と隣接する全 Hom の依存積へ厳密に回収する。
方針：元の mkOfObjOfMapSucc と射列の隣接射による外延性を使う。
規約：長さ零も含み、全頂点と隣接射を保持する。
使われ方：DK10.6(ii)の固定頂点列ごとの Hom 因子分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ChainCoordinates
open CategoryTheory
variable {C : Type u} [Category.{u} C] (n : ℕ)
abbrev Data := Σ x : Fin (n + 1) → C, ∀ i : Fin n, x i.castSucc ⟶ x i.succ

def equivalence : ComposableArrows C n ≃ Data (C := C) n where
  toFun c := ⟨c.obj, fun i => c.map (homOfLE (Fin.castSucc_le_succ i))⟩
  invFun e := ComposableArrows.mkOfObjOfMapSucc e.1 e.2
  left_inv c := by
    refine ComposableArrows.ext (fun _ => rfl) ?_
    intro i hi
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact ComposableArrows.mkOfObjOfMapSucc_map_succ c.obj
      (fun j => c.map (homOfLE (Fin.castSucc_le_succ j))) i hi
  right_inv e := by
    rcases e with ⟨x, h⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    funext i
    exact ComposableArrows.mkOfObjOfMapSucc_map_succ x h i.val i.isLt

variable {n} {D : Type u} [Category.{u} D]

def map (H : C ⥤ D) (x : Data (C := C) n) : Data (C := D) n :=
  ⟨H.obj ∘ x.1, fun i => H.map (x.2 i)⟩

lemma equivalence_map (H : C ⥤ D) (c : ComposableArrows C n) :
    equivalence n (c ⋙ H) = map H (equivalence n c) := rfl

lemma map_id (x : Data (C := C) n) : map (𝟭 C) x = x := rfl

lemma map_comp {E : Type u} [Category.{u} E] (H : C ⥤ D) (K : D ⥤ E)
    (x : Data (C := C) n) : map (H ⋙ K) x = map K (map H x) := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ChainCoordinates
