module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PathMaximum

/-!
概要：coherent nerve の長い Hom の path を、内点の二値フラグで表示する。
方針：両端を必ず含め、フラグ一の内点だけを含める。フラグの順序は path の包含になる。
規約：Mathlib の包含方向。使われ方：二単体の Hom 経路と三単体の Hom 正方形の読み取り。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates

/-- 同じ二端点の path の包含の間の平行射は一意。 -/
instance pathHom_subsingleton {J : Type u} [LinearOrder J] {i j : J} (P Q : Path i j) :
    Subsingleton (P ⟶ Q) :=
  ⟨fun f g ↦ by
    rcases f with ⟨⟨⟨f⟩⟩⟩
    rcases g with ⟨⟨⟨g⟩⟩⟩
    rfl⟩

/-- 両端と、二値フラグ一の内点だけからなる長い path。 -/
def flaggedPath {n : ℕ} (a : Fin n → Fin 2) :
    Path (ULift.up (0 : Fin (n + 2)) : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))) where
  I := {k | k.down = 0 ∨ k.down = Fin.last (n + 1) ∨
    ∃ r : Fin n, k.down = r.succ.castSucc ∧ a r = 1}
  left := Or.inl rfl
  right := Or.inr (Or.inl rfl)
  left_le k _ := Fin.zero_le k.down
  le_right k _ := Fin.le_last k.down

/-- 全てのフラグを増やすと、元の path から新しい path への包含射を得る。 -/
def flaggedPathMap {n : ℕ} {a b : Fin n → Fin 2} (h : ∀ r, a r ≤ b r) :
    flaggedPath.{u} a ⟶ flaggedPath b :=
  ⟨⟨⟨by
    intro k hk
    rcases hk with hk | hk | ⟨r, hr, ha⟩
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
    · refine Or.inr (Or.inr ⟨r, hr, ?_⟩)
      exact le_antisymm (Fin.le_last (b r)) (ha ▸ h r)⟩⟩⟩

/-- フラグが同じなら、構成した包含は元の path の恒等射。 -/
lemma flaggedPathMap_id {n : ℕ} (a : Fin n → Fin 2) :
    flaggedPathMap.{u} (fun r ↦ le_refl (a r)) = 𝟙 (flaggedPath a) :=
  Subsingleton.elim _ _

/-- フラグの二段階の包含は、元の path の包含の合成を保つ。 -/
lemma flaggedPathMap_comp {n : ℕ} {a b c : Fin n → Fin 2}
    (h : ∀ r, a r ≤ b r) (k : ∀ r, b r ≤ c r) :
    flaggedPathMap.{u} h ≫ flaggedPathMap k = flaggedPathMap (fun r ↦ (h r).trans (k r)) :=
  Subsingleton.elim _ _

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
