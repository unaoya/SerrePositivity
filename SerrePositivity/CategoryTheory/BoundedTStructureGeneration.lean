module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# heart からの有限 Postnikov 生成

heart を含む三角部分圏は、t 有界な全対象を含む。
有限な次数幅に関する帰納法を明示し、充満な三角関手の本質像にも適用する。
これは heart の持ち上げを有界対象へ拡張する一般的な接続である。
適用時には関手の充満性と heart の持ち上げを別途証明する必要がある。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] (t : TStructure C) (P : ObjectProperty C)
  [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
  (hh : t.heart ≤ P)

include hh in
omit [IsTriangulated C] in
/-- heart を含みシフトで閉じた部分圏は、単一次数に集中した対象を含む。 -/
lemma pure_mem_of_heart (X : C) (n : ℤ) [t.IsGE X n] [t.IsLE X n] : P X := by
  have := t.isGE_shift X n n 0 (add_zero n)
  have := t.isLE_shift X n n 0 (add_zero n)
  have h : P (X⟦n⟧) := hh _ ⟨t.le_of_isLE _ 0, t.ge_of_isGE _ 0⟩
  exact (P.prop_shift_iff_of_isStableUnderShift X n).1 h

include hh in
set_option backward.defeqAttrib.useBackward true in
/-- 有限な次数幅の対象は、heart と有限回の切り詰め三角形から生成される。 -/
lemma finiteAmplitude_mem_of_heart (w : ℕ) (X : C) (a : ℤ)
    [t.IsGE X a] [t.IsLE X (a + w)] : P X := by
  induction w generalizing X a with
  | zero =>
    have : t.IsLE X a := by simpa using (inferInstance : t.IsLE X (a + (0 : ℕ)))
    exact pure_mem_of_heart t P hh X a
  | succ w ih =>
    let n : ℤ := a + w
    let T := (t.triangleLEGE n (n + 1) rfl).obj X
    have hle : t.IsLE X (n + 1) := by
      convert (inferInstance : t.IsLE X (a + (w + 1 : ℕ))) using 1
      dsimp [n]
      omega
    have : t.IsGE T.obj₁ a := by dsimp [T]; infer_instance
    have : t.IsLE T.obj₁ (a + w) := by dsimp [T, n]; infer_instance
    have : t.IsGE T.obj₃ (n + 1) := by dsimp [T]; infer_instance
    have : t.IsLE T.obj₃ (n + 1) := by dsimp [T]; infer_instance
    exact P.ext_of_isTriangulatedClosed₂ T (t.triangleLEGE_distinguished n (n + 1) rfl X)
      (ih T.obj₁ a) (pure_mem_of_heart t P hh T.obj₃ (n + 1))

include hh in
/-- heart を含む三角部分圏は全ての t 有界対象を含む。 -/
lemma bounded_le_of_heart : t.bounded ≤ P := by
  rintro X ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have := t.isLE_of_le X b (a + (b - a).toNat) (by omega)
  exact finiteAmplitude_mem_of_heart t P hh (b - a).toNat X a

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : D ⥤ C) [F.CommShift ℤ] [F.IsTriangulated] [F.Full]

/-- 充満な三角関手で heart が持ち上がれば、全 t 有界対象が持ち上がる。 -/
lemma bounded_mem_essImage_of_heart (hheart : t.heart ≤ F.essImage) :
    t.bounded ≤ F.essImage := bounded_le_of_heart t F.essImage hheart

/-- 有界 t 構造の heart に対する持ち上げから、本質的全射性を得る。 -/
lemma essSurj_of_bounded_of_heart (hb : ∀ X : C, t.bounded X)
    (hheart : t.heart ≤ F.essImage) : F.EssSurj :=
  ⟨fun X ↦ bounded_mem_essImage_of_heart t F hheart X (hb X)⟩

end SerrePositivity
