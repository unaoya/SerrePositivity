module

public import SerrePositivity.KST.DerivedGeometry.AdjunctionCompact
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
概要：全シフトの Hom による零対象検出を保存的な随伴で移す。
方針：随伴とシフト同型で Hom を戻し、零自己射の同型反映を使う。
規約：幾何的な生成定理や導来随伴の存在を未証明のフィールドにしない。
使われ方：Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の T1 の形式的部分。
-/

@[expose] public section
noncomputable section

universe v₁ v₂ w₁ w₂

namespace SerrePositivity.KST.DerivedGeometry

open CategoryTheory Limits

variable {C : Type w₁} [Category.{v₁} C] [Preadditive C]
  {D : Type w₂} [Category.{v₂} D] [Preadditive D]

/--
概要：保存的な零射保存関手は零対象を反映する。
方針：像の零自己射を恒等射と同定し、その同型性を反映する。
規約：関手の忠実性は不要。
使われ方：Toën §3.2 の導来忘却による生成性の判定。
-/
lemma isZero_of_conservative (G : D ⥤ C) [G.PreservesZeroMorphisms]
    [G.ReflectsIsomorphisms] {Y : D} (h : IsZero (G.obj Y)) : IsZero Y := by
  have : IsIso (G.map (0 : Y ⟶ Y)) := by
    rw [G.map_zero, ← h.eq_zero_of_src (𝟙 _)]
    infer_instance
  have : IsIso (0 : Y ⟶ Y) := isIso_of_reflects_iso (0 : Y ⟶ Y) G
  exact IsZero.of_epi_zero Y Y

/--
概要：全整数シフトからの Hom の消滅で零対象を検出する族。
方針：各 Hom の全ての射が零であることを条件とする。
規約：古典的生成の有限三角閉包とは別の、局所化で使う生成判定。
使われ方：Bondal–van den Bergh Thm 3.1.1、Neeman 1992 Thm 2.1、T1。
-/
def shiftZeroDetecting [HasShift C ℤ] (P : ObjectProperty C) : Prop :=
  ∀ Y, (∀ X, P X → ∀ (n : ℤ) (f : X⟦n⟧ ⟶ Y), f = 0) → IsZero Y

/--
概要：保存的右随伴を持つシフト可換な左随伴は零対象検出族を移す。
方針：シフト同型と随伴の Hom 同値で検出条件を元の圏へ戻す。
規約：右随伴の忠実性や係数の平坦性は要求しない。
使われ方：Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の係数つき生成。
-/
lemma shiftZeroDetecting_leftAdjoint [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [F.CommShift ℤ]
    [G.ReflectsIsomorphisms] (adj : F ⊣ G) {P : ObjectProperty C}
    (hP : shiftZeroDetecting P) :
    shiftZeroDetecting (fun Z => ∃ X, P X ∧ Nonempty (F.obj X ≅ Z)) := by
  let := adj.right_adjoint_additive
  intro Y hY
  apply isZero_of_conservative G
  apply hP
  intro X hX n f
  let e := (F.commShiftIso n).app X
  let g := (adj.homEquiv (X⟦n⟧) Y).symm f
  have hg : e.inv ≫ g = 0 := hY (F.obj X) ⟨X, hX, ⟨Iso.refl _⟩⟩ n _
  have hg' : g = 0 := by
    apply (cancel_epi e.inv).mp
    simpa using hg
  have hf := congrArg (adj.homEquiv (X⟦n⟧) Y) hg'
  simpa only [g, Equiv.apply_symm_apply, adj.homAddEquiv_zero] using hf

end SerrePositivity.KST.DerivedGeometry
