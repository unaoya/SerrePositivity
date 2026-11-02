module

public import SerrePositivity.Asymptotic.RankQuotient
public import SerrePositivity.Asymptotic.NormalizedLimit
public import SerrePositivity.PerfectComplex.AsymptoticLengthBounds
public import SerrePositivity.CategoryTheory.HomotopyProperty
public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.CategoryTheory.IteratedCone
public import SerrePositivity.CategoryTheory.ScalarSupport

/-! # 自由複体の列の Koszul 構成

## 概要

自由列の複体から Koszul の長さの評価に要る共通の次数範囲と基底を取り出して長さの O(s)・o(s) 評価を得、自由複体の列の具体的な Koszul 構成と、その一様な台と商で零になるスカラー作用を与え、共通の反復錐定理へ渡す。

## 方針

台と零作用は三角関手の像でだけ要求する。

## 規約

元の複体の列に一様な台を加える必要はない。

## 使われ方

`Completed`・`Minimal`、Paper/Section4。
-/

@[expose] public noncomputable section

universe u

section SequenceKoszulBoundsPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter Asymptotics

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 有界性から、定量評価用の半開次数区間を列全体に共通して選べる。 -/
lemma sequenceComplex_uniform_interval (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P) :
    ∃ (a : ℤ) (w : ℕ), ∀ n i, (i < a ∨ a + w ≤ i) →
      IsZero (((evaluateComplex n).obj P).X i) := by
  obtain ⟨a, b, ha, hb⟩ := hP
  refine ⟨a, (b - a + 1).toNat, fun n i hi ↦ ?_⟩
  apply (FreeSequence.evaluation n).map_isZero
  rcases hi with hi | hi
  · exact P.isZero_of_isStrictlyGE a i hi
  · exact P.isZero_of_isStrictlyLE b i (by omega)

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (x : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
  (hfin : ∀ i, lam.len ((koszulComplex x).homology i) ≠ ⊤)

include hfg hJ hfin in
/-- 実数化する前の各段の Koszul ホモロジーの長さは有限である。 -/
lemma sequenceKoszulHomology_ne_top (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P) (n : ℕ) (q : ℤ) :
    lam.len ((koszulComplexOn x ((evaluateComplex n).obj P)).homology q) ≠ ⊤ := by
  obtain ⟨a, w, hbound⟩ := sequenceComplex_uniform_interval P hP
  exact ne_top_of_le_ne_top (ennreal_sum_nsmul_ne_top (Finset.range w)
    (fun j ↦ lam.len ((koszulComplex x).homology (q - (a + j)))) (fun _ _ ↦ hfin _)
    (fun j ↦ (P.X (a + j)).rank n))
    (lambdaHomology_koszulComplexOn_le_sum lam hfg x hJ a w
      (fun i ↦ (P.X i).rank n) ((evaluateComplex n).obj P) (hbound n)
      (fun _ _ _ ↦ ⟨Iso.refl _⟩) q)

include hfg hJ hfin in
/-- 共通有界な自由列に Koszul 関手を施すと、各次数の長さは `O(s)` となる。 -/
lemma sequenceKoszulHomology_isBigO (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P) (q : ℤ) :
    (fun n ↦ (lam.len ((koszulComplexOn x ((evaluateComplex n).obj P)).homology q)).toReal)
      =O[atTop] (fun n ↦ (s n : ℝ)) := by
  obtain ⟨a, w, hbound⟩ := sequenceComplex_uniform_interval P hP
  exact lambdaHomology_koszulComplexOn_isBigO lam hfg x hJ hfin a w
    (fun n i ↦ (P.X i).rank n) (fun n ↦ (evaluateComplex n).obj P) hbound
    (fun _ _ _ _ ↦ ⟨Iso.refl _⟩) _ (fun i _ _ ↦ (P.X i).rank_isBigO) q

include hfg hJ hfin in
/-- 小さいランクの共通有界複体では、Koszul ホモロジーの長さも通常の `o(s)` となる。 -/
lemma sequenceKoszulHomology_isLittleO (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : rankSmallComplex P) (q : ℤ) :
    (fun n ↦ (lam.len ((koszulComplexOn x ((evaluateComplex n).obj P)).homology q)).toReal)
      =o[atTop] (fun n ↦ (s n : ℝ)) := by
  obtain ⟨a, w, hbound⟩ := sequenceComplex_uniform_interval P hP.1
  exact lambdaHomology_koszulComplexOn_isLittleO lam hfg x hJ hfin a w
    (fun n i ↦ (P.X i).rank n) (fun n ↦ (evaluateComplex n).obj P) hbound
    (fun _ _ _ _ ↦ ⟨Iso.refl _⟩) _ (fun i _ _ ↦ hP.2 i) q

include hfg hJ hfin in
/-- 小さいランクの複体の Koszul ホモロジーは、正規化超極限で零になる。 -/
lemma sequenceKoszulHomology_normalizedLimit_eq_zero
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (P : CochainComplex (FreeSequence R s) ℤ) (hP : rankSmallComplex P) (q : ℤ) :
    normalizedLimit U s
      (fun n ↦ (lam.len ((koszulComplexOn x ((evaluateComplex n).obj P)).homology q)).toReal)
      = 0 :=
  normalizedLimit_eq_zero_of_isLittleO U hU s _
    (sequenceKoszulHomology_isLittleO lam hfg x hJ hfin P hP q)

end SerrePositivity.Asymptotic

end SequenceKoszulBoundsPart

section SequenceKoszulPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 自由列の圏でスカラー作用の錐を反復する。 -/
noncomputable def sequenceKoszul : {n : ℕ} → (Fin n → R) →
    CochainComplex (FreeSequence R s) ℤ → CochainComplex (FreeSequence R s) ℤ
  | 0, _, K => K
  | n + 1, x, K =>
      CochainComplex.mappingCone (x (Fin.last n) • 𝟙 (sequenceKoszul (Fin.init x) K))

lemma sequenceKoszul_bounded {n : ℕ} (x : Fin n → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K) :
    strictlyBoundedComplex _ (sequenceKoszul x K) := by
  induction n with
  | zero => exact hK
  | succ n ih => exact strictlyBoundedComplex_mappingCone _ _ (ih _) (ih _)

/-- 各段への評価は既存の係数つき Koszul 複体と一致する。 -/
noncomputable def evaluateSequenceKoszulIso : ∀ {m : ℕ} (x : Fin m → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (n : ℕ),
    (evaluateComplex n).obj (sequenceKoszul x K) ≅
      koszulComplexOn x ((evaluateComplex n).obj K)
  | 0, _, _, _ => Iso.refl _
  | m + 1, x, K, n => by
      let a := x (Fin.last m)
      let P := sequenceKoszul (Fin.init x) K
      have : (evaluateComplex (R := R) (s := s) n).Linear R :=
        inferInstanceAs (((FreeSequence.evaluation n).mapHomologicalComplex (.up ℤ)).Linear R)
      let e := CochainComplex.mappingCone.mapHomologicalComplexIso (a • 𝟙 P)
        (FreeSequence.evaluation n)
      have h : (evaluateComplex n).map (a • 𝟙 P) = smulId a ((evaluateComplex n).obj P) := by
        rw [Functor.map_smul, (evaluateComplex n).map_id]
        rfl
      let e' := eqToIso (congrArg
        (fun f : (evaluateComplex n).obj P ⟶ (evaluateComplex n).obj P ↦
          CochainComplex.mappingCone f) h)
      exact e ≪≫ e' ≪≫
        (scalarConeFunctor a).mapIso (evaluateSequenceKoszulIso (Fin.init x) K n)

/-- 有界自由列の射の具体的な写像錐三角形。 -/
@[implicit_reducible]
noncomputable def sequenceConeTriangle {K L : CochainComplex (FreeSequence R s) ℤ}
    (f : K ⟶ L) (hK : strictlyBoundedComplex _ K) (hL : strictlyBoundedComplex _ L) :
    Triangle (SequenceHomotopy R s) :=
  fullSubcategoryTriangle (boundedHomotopyProperty (FreeSequence R s))
    (CochainComplex.mappingCone.triangleh f)
    ((boundedHomotopyProperty_quotient _ K).mpr hK)
    ((boundedHomotopyProperty_quotient _ L).mpr hL)
    ((boundedHomotopyProperty_quotient _ _).mpr (strictlyBoundedComplex_mappingCone _ f hK hL))

lemma sequenceConeTriangle_distinguished {K L : CochainComplex (FreeSequence R s) ℤ}
    (f : K ⟶ L) (hK : strictlyBoundedComplex _ K) (hL : strictlyBoundedComplex _ L) :
    sequenceConeTriangle f hK hL ∈ distTriang (SequenceHomotopy R s) :=
  fullSubcategoryTriangle_distinguished _ _ _ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)

@[simp] lemma sequenceConeTriangle_smul_mor₁
    (a : R) (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K) :
    (sequenceConeTriangle (a • 𝟙 K) hK hK).mor₁ = a • 𝟙 (sequenceHomotopyObj K hK) := by
  apply ObjectProperty.hom_ext
  change (HomotopyCategory.quotient _ _).map (a • 𝟙 K) = a • 𝟙 _
  rw [Functor.map_smul, (HomotopyCategory.quotient _ _).map_id]
  rfl

end SerrePositivity.Asymptotic

end SequenceKoszulPart

section SequenceKoszulSupportPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 係数複体の台によらず、Koszul 複体列は一様に支持される。 -/
lemma sequenceKoszul_supported {n : ℕ} (x : Fin n → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K) :
    scalarSupported x (sequenceHomotopyObj (sequenceKoszul x K)
      (sequenceKoszul_bounded x K hK)) := by
  induction n with
  | zero => exact ⟨1, by omega, fun j ↦ j.elim0⟩
  | succ n ih =>
      let P := sequenceKoszul (Fin.init x) K
      let hP := sequenceKoszul_bounded (Fin.init x) K hK
      let a := x (Fin.last n)
      let T := sequenceConeTriangle (a • 𝟙 P) hP hP
      have hT := sequenceConeTriangle_distinguished (a • 𝟙 P) hP hP
      have hi := scalarSupported_triangle (Fin.init x) T hT (ih _) (ih _)
      have ha : (a * a) • 𝟙 T.obj₃ = 0 :=
        smul_mul_self_id_eq_zero T hT a
          (by
            change (a • 𝟙 (sequenceHomotopyObj P hP)) ≫ T.mor₂ = 0
            rw [← sequenceConeTriangle_smul_mor₁ a P hP]
            exact comp_distTriang_mor_zero₁₂ T hT)
          (by
            change T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map
              (a • 𝟙 (sequenceHomotopyObj P hP)) = 0
            rw [← sequenceConeTriangle_smul_mor₁ a P hP]
            exact comp_distTriang_mor_zero₃₁ T hT)
      exact scalarSupported_fin_succ x T.obj₃ hi 2 (by omega) (by simpa only [pow_two] using ha)

/-- 共通の正の冪で作った Koszul 複体も元のパラメータ系で一様に支持される。 -/
lemma sequenceKoszul_pow_supported {n : ℕ} (x : Fin n → R) (v : ℕ) (hv : 0 < v)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K) :
    scalarSupported x (sequenceHomotopyObj (sequenceKoszul (fun j ↦ x j ^ v) K)
      (sequenceKoszul_bounded _ K hK)) := by
  obtain ⟨w, hw, h⟩ := sequenceKoszul_supported (fun j ↦ x j ^ v) K hK
  exact ⟨v * w, Nat.mul_pos hv hw, fun j ↦ by simpa only [pow_mul] using h j⟩

variable {D : Type*} [Category* D] [Preadditive D] [Linear R D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] [Pretriangulated D]
  (F : SequenceHomotopy R s ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]

omit [F.Linear R] in
/-- Koszul の反復は、像で既に成り立つ支持条件を保つ。 -/
lemma sequenceKoszul_map_supported {e n : ℕ} (z : Fin e → R) (x : Fin n → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (F.obj (sequenceHomotopyObj K hK))) :
    scalarSupported z (F.obj (sequenceHomotopyObj (sequenceKoszul x K)
      (sequenceKoszul_bounded x K hK))) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      let P := sequenceKoszul (Fin.init x) K
      let hP := sequenceKoszul_bounded (Fin.init x) K hK
      let T := sequenceConeTriangle (x (Fin.last n) • 𝟙 P) hP hP
      exact scalarSupported_triangle z (F.mapTriangle.obj T)
        (F.map_distinguished T (sequenceConeTriangle_distinguished _ _ _)) (ih _) (ih _)

/-- パラメータが像で零なら、反復する錐は元の消去スカラーをそのまま保つ。 -/
lemma sequenceKoszul_map_smul_zero {n : ℕ} (x : Fin n → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (hx : ∀ j, x j • 𝟙 (F.obj (sequenceHomotopyObj K hK)) = 0)
    (a : R) (ha : a • 𝟙 (F.obj (sequenceHomotopyObj K hK)) = 0) :
    a • 𝟙 (F.obj (sequenceHomotopyObj (sequenceKoszul x K)
      (sequenceKoszul_bounded x K hK))) = 0 := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih =>
      let P := sequenceKoszul (Fin.init x) K
      let hP := sequenceKoszul_bounded (Fin.init x) K hK
      let c := x (Fin.last n)
      let T := sequenceConeTriangle (c • 𝟙 P) hP hP
      have hT := F.map_distinguished T (sequenceConeTriangle_distinguished _ _ _)
      have hc := ih (Fin.init x) (fun j ↦ hx j.castSucc) c (hx (Fin.last n))
      have ha' := ih (Fin.init x) (fun j ↦ hx j.castSucc) a ha
      have hf : (F.mapTriangle.obj T).mor₁ = 0 := by
        change F.map (show sequenceHomotopyObj P hP ⟶ sequenceHomotopyObj P hP from
          (sequenceConeTriangle (c • 𝟙 P) hP hP).mor₁) = 0
        rw [sequenceConeTriangle_smul_mor₁, F.map_smul, F.map_id]
        exact hc
      exact scalar_zero_on_zero_cone (F.mapTriangle.obj T) hT hf a ha' ha'

end SerrePositivity.Asymptotic

end SequenceKoszulSupportPart

section KoszulTowerPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}
  {D : Type*} [Category* D] [Preadditive D] [Linear R D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] [Pretriangulated D]
  (F : SequenceHomotopy R s ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]
  {e : ℕ} (z : Fin e → R) (x : ℕ → R)
  (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
  (h : scalarSupported z (F.obj (sequenceHomotopyObj K hK)))

/-- 各段を、関手の像における支持部分圏の対象とする。 -/
noncomputable def sequenceKoszulTowerObj (k : ℕ) : (scalarSupported (C := D) z).FullSubcategory :=
  ⟨F.obj (sequenceHomotopyObj (sequenceKoszul (fun j : Fin k ↦ x j) K)
    (sequenceKoszul_bounded _ K hK)), sequenceKoszul_map_supported F z _ K hK h⟩

/-- 実際の Koszul の写像錐を三角関手で送り、支持部分圏へ制限する。 -/
@[implicit_reducible]
noncomputable def sequenceKoszulTowerTriangle (k : ℕ) :
    Triangle (scalarSupported (C := D) z).FullSubcategory :=
  let P := sequenceKoszul (fun j : Fin k ↦ x j) K
  let hP := sequenceKoszul_bounded (fun j : Fin k ↦ x j) K hK
  fullSubcategoryTriangle (scalarSupported (C := D) z)
    (F.mapTriangle.obj (sequenceConeTriangle (x k • 𝟙 P) hP hP))
    (sequenceKoszulTowerObj F z x K hK h k).property
    (sequenceKoszulTowerObj F z x K hK h k).property
    (sequenceKoszulTowerObj F z x K hK h (k + 1)).property

omit [F.Linear R] in
lemma sequenceKoszulTowerTriangle_distinguished (k : ℕ) :
    sequenceKoszulTowerTriangle F z x K hK h k ∈ distTriang _ :=
  fullSubcategoryTriangle_distinguished _ _ _ _ _
    (F.map_distinguished _ (sequenceConeTriangle_distinguished _ _ _))

@[simp] lemma sequenceKoszulTowerTriangle_mor₁ (k : ℕ) :
    (sequenceKoszulTowerTriangle F z x K hK h k).mor₁ =
      x k • 𝟙 (sequenceKoszulTowerObj F z x K hK h k) := by
  apply ObjectProperty.hom_ext
  let P := sequenceKoszul (fun j : Fin k ↦ x j) K
  let hP := sequenceKoszul_bounded (fun j : Fin k ↦ x j) K hK
  change F.map (show sequenceHomotopyObj P hP ⟶ sequenceHomotopyObj P hP from
    (sequenceConeTriangle (x k • 𝟙 P) hP hP).mor₁) = _
  rw [sequenceConeTriangle_smul_mor₁, F.map_smul, F.map_id]
  rfl

lemma sequenceKoszulTowerTriangle_mk_distinguished (k : ℕ) :
    Triangle.mk (x k • 𝟙 (sequenceKoszulTowerObj F z x K hK h k))
      (sequenceKoszulTowerTriangle F z x K hK h k).mor₂
      (sequenceKoszulTowerTriangle F z x K hK h k).mor₃ ∈ distTriang _ := by
  rw [← sequenceKoszulTowerTriangle_mor₁ F z x K hK h k]
  exact sequenceKoszulTowerTriangle_distinguished F z x K hK h k

/-- 商での零作用を使い、具体的な Koszul 列を零射の錐の列にする。 -/
lemma sequenceKoszulTower_zero_triangles (n : ℕ)
    (hx : ∀ j < n, x j • 𝟙 (F.obj (sequenceHomotopyObj K hK)) = 0) :
    ∀ k < n, Triangle.mk (0 : sequenceKoszulTowerObj F z x K hK h k ⟶ _)
      (sequenceKoszulTowerTriangle F z x K hK h k).mor₂
      (sequenceKoszulTowerTriangle F z x K hK h k).mor₃ ∈ distTriang _ :=
  iteratedScalarCone_zero_triangles (sequenceKoszulTowerObj F z x K hK h)
    (fun k ↦ (sequenceKoszulTowerTriangle F z x K hK h k).mor₂)
    (fun k ↦ (sequenceKoszulTowerTriangle F z x K hK h k).mor₃) n x
    (fun k _ ↦ sequenceKoszulTowerTriangle_mk_distinguished F z x K hK h k)
    (fun j hj ↦ ObjectProperty.hom_ext _ (hx j hj))

variable {A : Type*} [Category* A] [Abelian A]
  (H : (scalarSupported (C := D) z).FullSubcategory ⥤ A)
  [H.IsHomological] [H.ShiftSequence ℤ]

/-- 実際の複体列の消滅は共通の対象としての消滅定理の適用。
元の列への一様支持も、長さの忠実性も仮定しない。 -/
theorem sequenceKoszulTower_vanishing (n : ℕ)
    (hx : ∀ j < n, x j • 𝟙 (F.obj (sequenceHomotopyObj K hK)) = 0)
    (a b : ℤ)
    (hKos : ∀ q, q < a ∨ b < q →
      IsZero ((H.shift q).obj (sequenceKoszulTowerObj F z x K hK h n)))
    (q : ℤ) (hq : q < a + n ∨ b < q) :
    IsZero ((H.shift q).obj (sequenceKoszulTowerObj F z x K hK h 0)) :=
  iteratedZeroCone_vanishing (sequenceKoszulTowerObj F z x K hK h)
    (fun k ↦ (sequenceKoszulTowerTriangle F z x K hK h k).mor₂)
    (fun k ↦ (sequenceKoszulTowerTriangle F z x K hK h k).mor₃) n
    (sequenceKoszulTower_zero_triangles F z x K hK h n hx) H a b hKos q hq

end SerrePositivity.Asymptotic

end KoszulTowerPart
