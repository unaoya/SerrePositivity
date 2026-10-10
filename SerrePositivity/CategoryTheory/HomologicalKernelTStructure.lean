module

public import SerrePositivity.CategoryTheory.VerdierTStructure
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# t 構造と両立するホモロジー関手の核による商

第零ホモロジー型の関手、すなわち非零次数側で消えるホモロジー関手について、
全シフトの核の分母が切り詰めで保たれることを証明する。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

variable {C A : Type*} [Category* C] [Category* A] [Abelian A]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (F : C ⥤ A) [F.IsHomological]

/-- ホモロジー関手をシフトと合成してもホモロジー関手である。 -/
instance homological_shift_comp (q : ℤ) : (shiftFunctor C q ⋙ F).IsHomological where
  exact T hT := by
    let := Functor.ShiftSequence.tautological F ℤ
    exact F.homologySequence_exact₂ T hT q

/-- 錐とその逆シフトの像が零なら、ホモロジー関手は第一の射を同型にする。 -/
lemma homological_isIso_map_of_cone_zeros (T : Triangle C) (hT : T ∈ distTriang C)
    (h₀ : IsZero (F.obj T.obj₃)) (hprev : IsZero (F.obj (T.obj₃⟦(-1 : ℤ)⟧))) :
    IsIso (F.map T.mor₁) := by
  have : Epi (F.map T.mor₁) :=
    (F.map_distinguished_exact T hT).epi_f (h₀.eq_of_tgt _ _)
  have : Mono (F.map T.mor₁) :=
    (F.map_distinguished_exact _ (inv_rot_of_distTriang T hT)).mono_g (hprev.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

variable (t : TStructure C)
  (hneg : ∀ (X : C), t.IsLE X (-1) → IsZero (F.obj X))
  (hpos : ∀ (X : C), t.IsGE X 1 → IsZero (F.obj X))

include hpos in
/-- 切り詰め境界の内側では、包含射はシフトした第零ホモロジーで同型になる。 -/
lemma homological_truncLEι_isIso (X : C) (q : ℤ) (hq : q ≤ 0) :
    IsIso ((shiftFunctor C q ⋙ F).map ((t.truncLEι 0).app X)) := by
  apply homological_isIso_map_of_cone_zeros (shiftFunctor C q ⋙ F)
    _ (t.triangleLEGE_distinguished 0 1 rfl X)
  · change IsZero (F.obj (((t.truncGE 1).obj X)⟦q⟧))
    apply hpos
    have := t.isGE_shift ((t.truncGE 1).obj X) 1 q (1 - q) (by omega)
    exact t.isGE_of_ge _ 1 (1 - q) (by omega)
  · change IsZero (F.obj ((((t.truncGE 1).obj X)⟦(-1 : ℤ)⟧)⟦q⟧))
    apply hpos
    have := t.isGE_shift ((t.truncGE 1).obj X) 1 (-1) 2 (by omega)
    have := t.isGE_shift (((t.truncGE 1).obj X)⟦(-1 : ℤ)⟧) 2 q (2 - q) (by omega)
    exact t.isGE_of_ge _ 1 (2 - q) (by omega)

include hneg in
omit [Abelian A] [F.IsHomological] in
/-- 境界の外側では、切り詰めた対象のホモロジーは零になる。 -/
lemma homological_truncLE_isZero (X : C) (q : ℤ) (hq : 0 < q) :
    IsZero ((shiftFunctor C q ⋙ F).obj ((t.truncLE 0).obj X)) := by
  apply hneg
  have := t.isLE_shift ((t.truncLE 0).obj X) 0 q (-q) (by omega)
  exact t.isLE_of_le _ (-q) (-1) (by omega)

include hneg hpos in
/-- 全シフトのホモロジーの核の分母は、非正切り詰めで保たれる。 -/
theorem homologicalKernel_truncLE {X Y : C} (f : X ⟶ Y)
    (hf : F.homologicalKernel.trW f) :
    F.homologicalKernel.trW ((t.truncLE 0).map f) := by
  let := Functor.ShiftSequence.tautological F ℤ
  rw [F.mem_homologicalKernel_trW_iff] at hf ⊢
  intro q
  change IsIso ((shiftFunctor C q ⋙ F).map ((t.truncLE 0).map f))
  let G := shiftFunctor C q ⋙ F
  by_cases hq : q ≤ 0
  · have : IsIso (G.map f) := hf q
    have := homological_truncLEι_isIso F t hpos X q hq
    have := homological_truncLEι_isIso F t hpos Y q hq
    have he : G.map ((t.truncLE 0).map f) =
        G.map ((t.truncLEι 0).app X) ≫ G.map f ≫ inv (G.map ((t.truncLEι 0).app Y)) := by
      rw [← cancel_mono (G.map ((t.truncLEι 0).app Y))]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← G.map_comp]
      rw [(t.truncLEι 0).naturality f]
      rfl
    rw [he]
    infer_instance
  · exact (homological_truncLE_isZero F t hneg X q (by omega)).isIso
      (homological_truncLE_isZero F t hneg Y q (by omega)) _

end SerrePositivity
