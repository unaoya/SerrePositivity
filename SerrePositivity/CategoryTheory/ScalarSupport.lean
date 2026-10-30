module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.EssentialImage
public import SerrePositivity.CategoryTheory.LinearScalar
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Finiteness.Ideal
public import SerrePositivity.CategoryTheory.Karoubi.Basic

/-! # スカラーの冪による台の条件

## 概要

線形三角圏で、スカラー r の冪が恒等射を消す対象のなす部分圏（スカラー支持）を定め、線形三角同値の支持部分圏への制限、台をもつ対象への射の Koszul 型の因子化、支持が生成イデアルの根基だけによること、スカラー恒等射と局所化の比較、冪等完備化後の支持対象の直和因子表示を与える。

## 方針

支持はスカラー恒等射の冪零性で定義する。根基による独立性は冪の比較から。冪零な自己準同型の補題（`smul_mul_self_id_eq_zero`・`pow_smul_id_eq_zero_of_le`）はこのファイルに置く（`LinearScalar` に置く。HomologicalAlgebra/NullHomotopy から下ろした）。

## 規約

Karoubi 完備化との両立は `Karoubi/Basic` を使う。

## 使われ方

Asymptotic の支持付きの階数の商、PerfectComplex・KST・DifferentialGraded の支持。
-/

@[expose] public noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

section SemilinearScalarPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

open CategoryTheory

variable {R S : Type*} [Ring R] [Ring S] (φ : R →+* S)
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear S D]

/-- 指定されたスカラーが恒等射を消すという性質は同型で移せる。 -/
lemma smul_id_zero_of_iso {X Y : C} (i : X ≅ Y) (r : R) (h : r • 𝟙 X = 0) :
    r • 𝟙 Y = 0 := by
  calc
    _ = i.inv ≫ (r • 𝟙 X) ≫ i.hom := by simp
    _ = 0 := by rw [h]; simp

/-- 恒等射のスカラー倍を保つという性質は対象の同型で移せる。 -/
lemma map_smul_id_of_iso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) (r : R)
    (h : F.map (r • 𝟙 X) = φ r • 𝟙 (F.obj X)) :
    F.map (r • 𝟙 Y) = φ r • 𝟙 (F.obj Y) := by
  apply (cancel_epi (F.map i.hom)).mp
  calc
    F.map i.hom ≫ F.map (r • 𝟙 Y) = F.map (r • 𝟙 X) ≫ F.map i.hom := by
      rw [← F.map_comp, ← F.map_comp]
      simp
    _ = _ := by rw [h]; simp

variable {B : Type u₃} [Category.{v₃} B] [Preadditive B] [Linear R B]

/-- 本質的全射な R 線形関手との合成上で確認したスカラーの式を降ろす。 -/
lemma map_smul_id_of_precomp (L : B ⥤ C) [L.Linear R] [L.EssSurj]
    (F : C ⥤ D) (H : B ⥤ D) (i : L ⋙ F ≅ H)
    (hH : ∀ (X : B) (r : R), H.map (r • 𝟙 X) = φ r • 𝟙 (H.obj X))
    (Y : C) (r : R) : F.map (r • 𝟙 Y) = φ r • 𝟙 (F.obj Y) := by
  obtain ⟨X, ⟨j⟩⟩ := Functor.EssSurj.mem_essImage L Y
  apply map_smul_id_of_iso φ F j r
  apply (cancel_mono (i.app X).hom).mp
  have h := i.hom.naturality (r • 𝟙 X)
  simpa only [Functor.comp_obj, Iso.app_hom, Functor.comp_map, Functor.map_smul, L.map_id, hH,
    Linear.comp_smul, Linear.smul_comp, Category.id_comp, Category.comp_id] using h

end SerrePositivity

end SemilinearScalarPart

section ScalarSupportPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

variable {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C]
  [Linear R C] {ι : Type*} (z : ι → R)

/-- 指定されたスカラーの共通の正の冪が対象の恒等射を零にする条件。 -/
def scalarSupported : ObjectProperty C :=
  fun X ↦ ∃ v : ℕ, 0 < v ∧ ∀ j, z j ^ v • 𝟙 X = 0

/-- 台の条件は直和因子に移る。消去指数は増やさなくてよい。 -/
instance : (scalarSupported (C := C) z).IsStableUnderRetracts where
  of_retract {X Y} r hY := by
    obtain ⟨v, hv, h⟩ := hY
    refine ⟨v, hv, fun j ↦ ?_⟩
    have he : z j ^ v • 𝟙 X = r.i ≫ (z j ^ v • 𝟙 Y) ≫ r.r := by simp
    rw [he, h j, zero_comp, comp_zero]

variable [HasZeroObject C]

instance : (scalarSupported (C := C) z).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, 1, by omega,
    fun _ ↦ (isZero_zero C).eq_of_src _ _⟩

omit [HasZeroObject C] in
/-- 線形関手は台の条件を保存する。 -/
lemma scalarSupported_map {D : Type*} [Category* D] [Preadditive D] [Linear R D]
    (F : C ⥤ D) [F.Additive] [F.Linear R] (X : C) (hX : scalarSupported z X) :
    scalarSupported z (F.obj X) := by
  obtain ⟨v, hv, h⟩ := hX
  refine ⟨v, hv, fun j ↦ ?_⟩
  simpa only [F.map_smul, F.map_id, F.map_zero] using congrArg F.map (h j)

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C]

instance : (scalarSupported (C := C) z).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift X hX := (ObjectProperty.prop_shift_iff _ _ _).2
        (scalarSupported_map z (shiftFunctor C n) X hX) }

/-- 完全三角形の初めの二対象の消去指数をそろえ、その二倍を錐の指数に使う。 -/
lemma scalarSupported_triangle (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : scalarSupported z T.obj₁) (h₂ : scalarSupported z T.obj₂) :
    scalarSupported z T.obj₃ := by
  obtain ⟨v, hv, h₁⟩ := h₁
  obtain ⟨w, hw, h₂⟩ := h₂
  refine ⟨max v w + max v w, by omega, fun j ↦ ?_⟩
  rw [pow_add]
  apply smul_mul_self_id_eq_zero T hT
  · rw [pow_smul_id_eq_zero_of_le (h₂ j) (le_max_right v w), zero_comp]
  · rw [pow_smul_id_eq_zero_of_le (h₁ j) (le_max_left v w),
      Functor.map_zero, comp_zero]

instance : (scalarSupported (C := C) z).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (scalarSupported_triangle z)

instance : (scalarSupported (C := C) z).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

end SerrePositivity

end ScalarSupportPart

section ScalarSupportEquivalencePart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {R : Type*} [CommRing R] {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
  (E : C ≌ D) [E.functor.Linear R] [E.functor.Additive] {e : ℕ} (z : Fin e → R)

lemma scalarSupported_equivalence_iff (X : C) :
    scalarSupported z (E.functor.obj X) ↔ scalarSupported z X := by
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, fun j ↦ E.functor.map_injective ?_⟩
    simpa only [Functor.map_smul, E.functor.map_id, E.functor.map_zero] using h j
  · exact scalarSupported_map z E.functor X

/-- 線形同値は同じパラメータで支持される部分圏の同値を誘導する。 -/
noncomputable def scalarSupportEquivalence :
    (scalarSupported (C := C) z).FullSubcategory ≌ (scalarSupported (C := D) z).FullSubcategory :=
  E.congrFullSubcategory (by ext X; exact scalarSupported_equivalence_iff E z X)

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] [Pretriangulated D]
  [E.functor.CommShift ℤ] [E.functor.IsTriangulated]

noncomputable instance scalarSupportEquivalence_functor_commShift :
    (scalarSupportEquivalence E z).functor.CommShift ℤ := by
  dsimp [scalarSupportEquivalence, CategoryTheory.Equivalence.congrFullSubcategory]
  infer_instance

instance scalarSupportEquivalence_functor_isTriangulated :
    (scalarSupportEquivalence E z).functor.IsTriangulated := by
  let P := scalarSupported (C := C) z
  let Q := scalarSupported (C := D) z
  exact (Functor.isTriangulated_iff_comp_right
    (Q.liftCompιIso (P.ι ⋙ E.functor) _)).mpr inferInstance

noncomputable instance scalarSupportEquivalence_inverse_commShift :
    (scalarSupportEquivalence E z).inverse.CommShift ℤ :=
  (scalarSupportEquivalence E z).commShiftInverse ℤ

instance scalarSupportEquivalence_commShift : (scalarSupportEquivalence E z).CommShift ℤ :=
  (scalarSupportEquivalence E z).commShift_of_functor ℤ

instance scalarSupportEquivalence_isTriangulated : (scalarSupportEquivalence E z).IsTriangulated :=
  CategoryTheory.Equivalence.IsTriangulated.mk' _ inferInstance

end SerrePositivity

end ScalarSupportEquivalencePart

section ScalarSupportLocalizationPart

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

end ScalarSupportLocalizationPart

section ScalarSupportRadicalPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
  {ι κ : Type*} (z : ι → R)

/-- 恒等射を消すスカラーは、すべての自己準同型を消す。 -/
lemma smul_id_eq_zero_iff_mem_annihilator (X : C) (a : R) :
    a • 𝟙 X = 0 ↔ a ∈ Module.annihilator R (X ⟶ X) := by
  rw [Module.mem_annihilator]
  constructor
  · intro ha f
    simpa only [Linear.smul_comp, Category.id_comp, zero_comp] using ha =≫ f
  · intro ha
    exact ha (𝟙 X)

/-- 有限パラメータ系の支持は、その生成イデアルが自己準同型の消去イデアルの根基に入ること。 -/
lemma scalarSupported_iff_le_radical_annihilator [Finite ι] (X : C) :
    scalarSupported z X ↔
      Ideal.span (Set.range z) ≤ (Module.annihilator R (X ⟶ X)).radical := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · rintro ⟨v, _, hv⟩
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨v, (smul_id_eq_zero_iff_mem_annihilator X _).mp (hv j)⟩
  · intro h
    have hj (j : ι) : ∃ v : ℕ, z j ^ v • 𝟙 X = 0 := by
      obtain ⟨v, hv⟩ := h (Ideal.subset_span ⟨j, rfl⟩)
      exact ⟨v, (smul_id_eq_zero_iff_mem_annihilator X _).mpr hv⟩
    choose v hv using hj
    refine ⟨Finset.univ.sup v + 1, by omega, fun j ↦ ?_⟩
    exact pow_smul_id_eq_zero_of_le (hv j)
      ((Finset.le_sup (Finset.mem_univ j)).trans (Nat.le_succ _))

/-- 生成イデアルの根基の包含に沿って、支持条件を移す。 -/
lemma scalarSupported_of_span_le_radical [Finite ι] [Finite κ] (w : κ → R)
    (h : Ideal.span (Set.range w) ≤ (Ideal.span (Set.range z)).radical)
    {X : C} (hX : scalarSupported z X) : scalarSupported w X := by
  rw [scalarSupported_iff_le_radical_annihilator] at hX ⊢
  exact h.trans (by simpa only [Ideal.radical_idem] using Ideal.radical_mono hX)

/-- 根基が同じ有限パラメータ系は、全く同じ支持部分圏を定める。 -/
lemma scalarSupported_eq_of_radical_eq [Finite ι] [Finite κ] (w : κ → R)
    (h : (Ideal.span (Set.range z)).radical = (Ideal.span (Set.range w)).radical) :
    scalarSupported (C := C) z = scalarSupported w := by
  funext X
  apply propext
  constructor
  · exact scalarSupported_of_span_le_radical z w (Ideal.le_radical.trans_eq h.symm)
  · exact scalarSupported_of_span_le_radical w z (Ideal.le_radical.trans_eq h)

end SerrePositivity

end ScalarSupportRadicalPart

section KaroubiScalarSupportPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Pretriangulated
open CategoryTheory.Limits

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- 完全三角形に対する Hom の完全性は、値域を形式的直和因子にしても成立する。 -/
lemma karoubi_yoneda_exact₂ (T : Triangle D) (hT : T ∈ distTriang D)
    (P : Karoubi D) (f : (toKaroubi D).obj T.obj₂ ⟶ P)
    (hf : (toKaroubi D).map T.mor₁ ≫ f = 0) :
    ∃ g : (toKaroubi D).obj T.obj₃ ⟶ P, f = (toKaroubi D).map T.mor₂ ≫ g := by
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T hT f.f (congrArg Karoubi.Hom.f hf)
  refine ⟨⟨g ≫ P.p, by simp⟩, ?_⟩
  apply Karoubi.hom_ext
  change f.f = T.mor₂ ≫ (g ≫ P.p)
  rw [← Category.assoc, ← hg, Karoubi.comp_p]

variable {R : Type*} [CommRing R] [Linear R D]
  {C : Type*} [Category* C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]

/-- 像の形式的直和因子が台をもてば、元の圏で台をもつ対象の像の直和因子にできる。 -/
theorem karoubi_scalarSupported_retract :
    ∀ {n : ℕ} (z : Fin n → R) (P : Karoubi D) (X : C),
      Retract P ((toKaroubi D).obj (F.obj X)) → scalarSupported z P →
      ∃ Z : C, scalarSupported z Z ∧
        Nonempty (Retract P ((toKaroubi D).obj (F.obj Z))) := by
  intro n
  induction n with
  | zero =>
      intro z P X r _
      exact ⟨X, ⟨1, by omega, fun j ↦ j.elim0⟩, ⟨r⟩⟩
  | succ n ih =>
      intro z P X r hP
      obtain ⟨v, hv, hP⟩ := hP
      obtain ⟨Z, hZ, ⟨r⟩⟩ := ih (Fin.init z) P X r ⟨v, hv, fun j ↦ hP j.castSucc⟩
      let c := z (Fin.last n) ^ v
      obtain ⟨W, g, h, hT⟩ := distinguished_cocone_triangle (c • 𝟙 Z)
      let T := Triangle.mk (c • 𝟙 Z) g h
      have hinit : scalarSupported (Fin.init z) W :=
        scalarSupported_triangle (Fin.init z) T hT hZ hZ
      have hc : (c * c) • 𝟙 W = 0 :=
        smul_mul_self_id_eq_zero T hT c
          (comp_distTriang_mor_zero₁₂ T hT) (comp_distTriang_mor_zero₃₁ T hT)
      have hr : (toKaroubi D).map (F.mapTriangle.obj T).mor₁ ≫ r.r = 0 := by
        apply Karoubi.hom_ext
        change F.map (c • 𝟙 Z) ≫ r.r.f = 0
        have hp : c • P.p = 0 := congrArg Karoubi.Hom.f (hP (Fin.last n))
        calc
          _ = r.r.f ≫ (c • P.p) := by simp
          _ = 0 := by rw [hp, comp_zero]
      obtain ⟨b, hb⟩ := karoubi_yoneda_exact₂ (F.mapTriangle.obj T)
        (F.map_distinguished T hT) P r.r hr
      refine ⟨W, scalarSupported_fin_succ z W hinit (v + v) (by omega) ?_,
        ⟨⟨r.i ≫ (toKaroubi D).map (F.map g), b, ?_⟩⟩⟩
      · simpa only [pow_add] using hc
      · change (r.i ≫ (toKaroubi D).map (F.mapTriangle.obj T).mor₂) ≫ b = _
        rw [Category.assoc, ← hb, r.retract]

/-- 本質的全射な三角関手に対して、冪等完備化後の全支持対象を表示する。 -/
theorem karoubi_scalarSupported_retract_image [F.EssSurj] {n : ℕ} (z : Fin n → R)
    (P : Karoubi D) (hP : scalarSupported z P) :
    ∃ Z : C, scalarSupported z Z ∧
      Nonempty (Retract P ((toKaroubi D).obj (F.obj Z))) := by
  let e := F.objObjPreimageIso P.X
  exact karoubi_scalarSupported_retract F z P (F.objPreimage P.X)
    ((karoubiRetract P).trans (Retract.ofIso ((toKaroubi D).mapIso e.symm))) hP

end SerrePositivity

end KaroubiScalarSupportPart
