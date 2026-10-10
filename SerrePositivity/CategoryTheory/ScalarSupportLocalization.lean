module

public import SerrePositivity.CategoryTheory.ScalarSupport
public import Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory

/-!
# 台をもつ対象への射の Koszul 型因子化

小部分圏の対象から台をもつ対象への射を、両方の条件を満たす対象を経由させる。
パラメータを一つずつ加え、スカラー作用の錐を取ることで証明する。
これにより支持部分圏の Verdier 商から全体の商への関手の完全忠実性が従う。
冪等完備化後の本質像の同定はこの結果に含めない。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C]
  [Linear R C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C]

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C] in
/-- 既存のパラメータと最後のパラメータの消去指数を最大値にそろえる。 -/
lemma scalarSupported_fin_succ {n : ℕ} (z : Fin (n + 1) → R) (X : C)
    (hX : scalarSupported (Fin.init z) X)
    (v : ℕ) (hv : 0 < v) (hlast : z (Fin.last n) ^ v • 𝟙 X = 0) :
    scalarSupported z X := by
  obtain ⟨w, hw, h⟩ := hX
  refine ⟨max w v, by omega, fun j ↦ ?_⟩
  induction j using Fin.lastCases with
  | last => exact pow_smul_id_eq_zero_of_le hlast (le_max_right w v)
  | cast j => exact pow_smul_id_eq_zero_of_le (h j) (le_max_left w v)

/-- 小部分圏の対象から台をもつ対象への射は、支持つき小対象を経由する。
反復する錐は小部分圏の中で取り、最後のスカラーの指数を二倍する。 -/
theorem scalarSupported_factorization (B : ObjectProperty C)
    [B.IsTriangulated] [B.IsClosedUnderIsomorphisms] :
    ∀ {n : ℕ} (z : Fin n → R) {X Y : C} (f : X ⟶ Y),
      B X → scalarSupported z Y →
      ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y),
        scalarSupported z Z ∧ B Z ∧ a ≫ b = f := by
  intro n
  induction n with
  | zero =>
      intro z X Y f hX _
      exact ⟨X, 𝟙 X, f, ⟨1, by omega, fun j ↦ j.elim0⟩, hX, by simp⟩
  | succ n ih =>
      intro z X Y f hX hY
      obtain ⟨v, hv, hY⟩ := hY
      obtain ⟨Z, a, b, hZ, hBZ, hab⟩ :=
        ih (Fin.init z) f hX ⟨v, hv, fun j ↦ hY j.castSucc⟩
      let c := z (Fin.last n) ^ v
      obtain ⟨W, g, h, hT⟩ := distinguished_cocone_triangle (c • 𝟙 Z)
      let T := Triangle.mk (c • 𝟙 Z) g h
      have hb : (c • 𝟙 Z) ≫ b = 0 := by
        rw [Linear.smul_comp, Category.id_comp, ← Category.comp_id b,
          ← Linear.comp_smul, hY (Fin.last n), comp_zero]
      obtain ⟨b', hb'⟩ := Triangle.yoneda_exact₂ T hT b hb
      have hW : B W := B.ext_of_isTriangulatedClosed₃ T hT hBZ hBZ
      have hinit : scalarSupported (Fin.init z) W :=
        scalarSupported_triangle (Fin.init z) T hT hZ hZ
      have hc : (c * c) • 𝟙 W = 0 :=
        smul_mul_self_id_eq_zero T hT c
          (comp_distTriang_mor_zero₁₂ T hT) (comp_distTriang_mor_zero₃₁ T hT)
      refine ⟨W, a ≫ g, b', scalarSupported_fin_succ z W hinit
        (v + v) (by omega) ?_, hW, ?_⟩
      · simpa only [pow_add] using hc
      · change (a ≫ T.mor₂) ≫ b' = f
        rw [Category.assoc, ← hb', hab]

instance scalarSupported_isVerdierRightLocalizing {n : ℕ} (z : Fin n → R)
    (B : ObjectProperty C) [B.IsTriangulated] [B.IsClosedUnderIsomorphisms] :
    (scalarSupported z).IsVerdierRightLocalizing B where
  fac f hX hY := scalarSupported_factorization B z f hX hY

variable {D : Type*} [Category* D] [Preadditive D] [Linear R D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]

/-- 関手の像で初めて台をもつ対象は、元の圏で台をもつ対象の像の直和因子になる。
射影の持ち上げを仮定せず、スカラー作用の錐と完全三角形の射の完全性だけを使う。 -/
theorem scalarSupported_retract_of_image :
    ∀ {n : ℕ} (z : Fin n → R) (X : C), scalarSupported z (F.obj X) →
      ∃ Z : C, scalarSupported z Z ∧ Nonempty (Retract (F.obj X) (F.obj Z)) := by
  intro n
  induction n with
  | zero =>
      intro z X _
      exact ⟨X, ⟨1, by omega, fun j ↦ j.elim0⟩, ⟨Retract.refl _⟩⟩
  | succ n ih =>
      intro z X hX
      obtain ⟨v, hv, hX⟩ := hX
      obtain ⟨Z, hZ, ⟨r⟩⟩ := ih (Fin.init z) X ⟨v, hv, fun j ↦ hX j.castSucc⟩
      let c := z (Fin.last n) ^ v
      obtain ⟨W, g, h, hT⟩ := distinguished_cocone_triangle (c • 𝟙 Z)
      let T := Triangle.mk (c • 𝟙 Z) g h
      have hinit : scalarSupported (Fin.init z) W :=
        scalarSupported_triangle (Fin.init z) T hT hZ hZ
      have hc : (c * c) • 𝟙 W = 0 :=
        smul_mul_self_id_eq_zero T hT c
          (comp_distTriang_mor_zero₁₂ T hT) (comp_distTriang_mor_zero₃₁ T hT)
      have hr : (F.mapTriangle.obj T).mor₁ ≫ r.r = 0 := by
        change F.map (c • 𝟙 Z) ≫ r.r = 0
        rw [F.map_smul, F.map_id, Linear.smul_comp, Category.id_comp,
          ← Category.comp_id r.r, ← Linear.comp_smul, hX (Fin.last n), comp_zero]
      obtain ⟨b, hb⟩ := Triangle.yoneda_exact₂ (F.mapTriangle.obj T)
        (F.map_distinguished T hT) r.r hr
      refine ⟨W, scalarSupported_fin_succ z W hinit (v + v) (by omega) ?_,
        ⟨⟨r.i ≫ F.map g, b, ?_⟩⟩⟩
      · simpa only [pow_add] using hc
      · change (r.i ≫ (F.mapTriangle.obj T).mor₂) ≫ b = _
        rw [Category.assoc, ← hb, r.retract]

/-- 本質的全射な三角関手では、台をもつ全対象を支持つき像の直和因子として表せる。 -/
theorem scalarSupported_retract_image [F.EssSurj] {n : ℕ} (z : Fin n → R) (Y : D)
    (hY : scalarSupported z Y) :
    ∃ Z : C, scalarSupported z Z ∧ Nonempty (Retract Y (F.obj Z)) := by
  let e := F.objObjPreimageIso Y
  have hX : scalarSupported z (F.obj (F.objPreimage Y)) :=
    (scalarSupported z).prop_of_iso e.symm hY
  obtain ⟨Z, hZ, ⟨r⟩⟩ := scalarSupported_retract_of_image F z _ hX
  exact ⟨Z, hZ, ⟨(Retract.ofIso e.symm).trans r⟩⟩

end SerrePositivity
