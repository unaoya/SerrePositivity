module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentSimplexLastPostCoordinates

/-!
概要：最後の対象の指定後合成は豊穣恒等と豊穣合成を保つ。
方針：最後へ入る場合の結合則と、逆向き Hom の空性を使う。
規約：元の全 Hom の指定値を保持。使われ方：合成 prism の高次拡張。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (s : (SimplicialNerve C) _⦋n + 1⦌) {Y : C}
  (g : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ ⟶ Y)
local notation "O(" i ")" => coherentSimplexLastPostObj s (Y := Y) i
local notation "H(" i "," j ")" => coherentSimplexLastPostHom s g i j

/-- 指定後合成による最後の対象の変更は、全対象で豊穣恒等を保つ。 -/
lemma coherentSimplexLastPostHom_id (i : Fin (n + 2)) :
    eId SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ≫ H(i,i) =
      eId SSet O(i) := by
  induction i using Fin.lastCases with
  | last =>
    simp -implicitDefEqProofs +instances [coherentSimplexLastPostHom, coherentSimplexLastPostObj]
  | cast i =>
    simp -implicitDefEqProofs +instances [coherentSimplexLastPostHom,
      coherentSimplexLastPostObj]

/-- 指定後合成による最後の対象の変更は、全 Hom の豊穣合成を保つ。 -/
lemma coherentSimplexLastPostHom_comp (i j k : Fin (n + 2)) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ H(i,k) =
      (H(i,j) ⊗ₘ H(j,k)) ≫ eComp SSet O(i) O(j) O(k) := by
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    induction k using Fin.lastCases
  case cast.cast.cast i j k =>
    apply (simplicialHom_map_comp_iff_normalized (coherentSimplexLastPostObj_cast s i)
      (coherentSimplexLastPostObj_cast s j) (coherentSimplexLastPostObj_cast s k) _ _ _ _).2
    simp only [coherentSimplexLastPostHom_cast_cast]
    exact s.map_comp _ _ _
  case cast.cast.last i j =>
    apply (simplicialHom_map_comp_iff_normalized (coherentSimplexLastPostObj_cast s i)
      (coherentSimplexLastPostObj_cast s j) (coherentSimplexLastPostObj_last s) _ _ _ _).2
    simp only [coherentSimplexLastPostHom_cast_cast, coherentSimplexLastPostHom_cast_last]
    rw [← Category.assoc, s.map_comp, Category.assoc, eComp_eHomWhiskerLeft]
    simp only [tensorHom_def, Category.assoc, whiskerLeft_comp]
  case last.last.last =>
    apply (simplicialHom_map_comp_iff_normalized (coherentSimplexLastPostObj_last s)
      (coherentSimplexLastPostObj_last s) (coherentSimplexLastPostObj_last s) _ _ _ _).2
    simp only [coherentSimplexLastPostHom_last_last]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    exact (simplicialHom_id_comp_app Y Y d _).symm
  case cast.last.last i =>
    apply (simplicialHom_map_comp_iff_normalized (coherentSimplexLastPostObj_cast s i)
      (coherentSimplexLastPostObj_last s) (coherentSimplexLastPostObj_last s) _ _ _ _).2
    simp only [coherentSimplexLastPostHom_cast_last, coherentSimplexLastPostHom_last_last]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    change ((s.map _ _ ≫ eHomWhiskerLeft SSet _ g).app d)
      ((eComp SSet _ _ _).app d (P, Q)) = _
    rw [thickeningHom_comp_end_right]
    exact (simplicialHom_comp_id_app _ Y d _).symm
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
  case last.last.cast k =>
    have h := Path.le (Q.obj 0)
    change n + 1 ≤ k.val at h
    omega
  case last.cast.last j =>
    have h := Path.le (P.obj 0)
    change n + 1 ≤ j.val at h
    omega
  case last.cast.cast j k =>
    have h := Path.le (P.obj 0)
    change n + 1 ≤ j.val at h
    omega
  case cast.last.cast i k =>
    have h := Path.le (Q.obj 0)
    change n + 1 ≤ k.val at h
    omega

end SerrePositivity.InfinityCategories.F2
