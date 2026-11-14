module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffinePolynomial
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDelta
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra

/-!
# affine Čech–Alexander 模型の構造射

## 概要
次数ごとの affine envelope が与えられたとき、単体の射から構造射を作る。

## 方針
座標の像を完備自由 δ 環の普遍性で指定し、envelope の普遍性で因子化する。

## 規約
環の向きの余単体的対象。差の座標は第 0 copy に対して取る。

## 使われ方
小さい affine Čech–Alexander 模型（BS 著者版 Remark 4.19）。
-/

public section
noncomputable section

universe u

open CategoryTheory
open SerrePositivity.DerivedCompletion
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- copy ごとの多項式座標の添字。 -/
abbrev AffineIndex (r n : ℕ) := ULift.{u} (Fin r × Fin (n+1))

/-- 指定した copy の初期座標。 -/
def affineVariable (r n : ℕ) (j : Fin r) (i : Fin (n+1)) : completedFreeDelta P (AffineIndex.{u} r n) :=
  pdCompletionUnit (RelativeFreeDeltaRing (R := A) (AffineIndex.{u} r n)) p (algebraMap A _ P.generator)
    (MvPolynomial.X (ULift.up (j, i), 0))

/-- 基底生成元と、第 0 copy との差で生成されるイデアル。 -/
def affineDifferenceIdeal (r n : ℕ) : Ideal (completedFreeDelta P (AffineIndex.{u} r n)) :=
  Ideal.span (insert (completedFreeDeltaBase P _ P.generator)
    (Set.range (fun ji : Fin r × Fin (n+1) =>
      affineVariable P r n ji.1 ji.2 - affineVariable P r n ji.1 0)))

/-- 次数 n の envelope とその座標を、site の対象の構造写像に結び付ける。 -/
structure AffineEnvelopeTerm (r n : ℕ) (κ : Cardinal.{u}) where
  X : PrismOver P (prismPolynomialCompletion P (Fin r)) κ
  η : completedFreeDelta P (AffineIndex.{u} r n) →+* X.B
  envelope : IsPrismaticEnvelope P (completedFreeDeltaStructure P _) (completedFreeDeltaBase P _)
    (completedFreeDeltaBase_isDeltaHom P _) (affineDifferenceIdeal P r n)
    (by unfold affineDifferenceIdeal; exact Ideal.subset_span (Set.mem_insert _ _)) X.Q η
  base_eq : η.comp (completedFreeDeltaBase P _) = X.toHom.toRingHom
  sec_X : ∀ j : Fin r, X.sec (prismPolynomialUnit P (Fin r) (MvPolynomial.X j)) =
    Ideal.Quotient.mk X.Q.ideal (η (affineVariable P r n j 0))

variable {r m n : ℕ} {κ : Cardinal.{u}}

private theorem affineVariable_eq (r n : ℕ) (j : Fin r) (i : Fin (n+1)) :
    affineVariable P r n j i =
      completedFreeDeltaVariable P (AffineIndex.{u} r n) ⟨(j, i)⟩ := rfl

private theorem affineTerm_difference_mem (Y : AffineEnvelopeTerm P r n κ)
    (j : Fin r) (i i' : Fin (n + 1)) :
    Y.η (affineVariable P r n j i) - Y.η (affineVariable P r n j i') ∈ Y.X.Q.ideal := by
  have h (a : Fin (n + 1)) :
      Y.η (affineVariable P r n j a) - Y.η (affineVariable P r n j 0) ∈ Y.X.Q.ideal := by
    rw [← map_sub]
    have hmem : affineVariable P r n j a - affineVariable P r n j 0 ∈
        affineDifferenceIdeal P r n := by
      unfold affineDifferenceIdeal
      exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨(j, a), rfl⟩)
    exact Y.envelope.map_le (Ideal.mem_map_of_mem _ hmem)
  have hsub := Y.X.Q.ideal.sub_mem (h i) (h i')
  rwa [sub_sub_sub_cancel_right] at hsub

private theorem affineTerm_existsUnique_eval (Y : AffineEnvelopeTerm P r n κ)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    ∃! g : completedFreeDelta P (AffineIndex.{u} r m) →+* Y.X.B,
      (completedFreeDeltaStructure P _).IsDeltaHom Y.X.Q.deltaStructure g ∧
      g.comp (completedFreeDeltaBase P _) = Y.X.toHom.toRingHom ∧
      ∀ j i, g (affineVariable P r m j i) =
        Y.η (affineVariable P r n j (θ.toOrderHom i)) := by
  let a (s : AffineIndex.{u} r m) := Y.η (affineVariable P r n s.down.1 (θ.toOrderHom s.down.2))
  obtain ⟨g, hg, hu⟩ := existsUnique_completedFreeDeltaHom P (AffineIndex.{u} r m)
    Y.X.Q.deltaStructure Y.X.toHom.toRingHom Y.X.toHom.map_delta Y.X.Q.complete_p
      Y.X.toHom.isModuleComplete_map_generator a
  refine ⟨g, ⟨hg.1, hg.2.1, fun j i => hg.2.2 ⟨(j, i)⟩⟩, ?_⟩
  intro f hf
  apply hu
  refine ⟨hf.1, hf.2.1, ?_⟩
  rintro ⟨⟨j, i⟩⟩
  exact hf.2.2 j i

private theorem affineTerm_sec_ext (Y : AffineEnvelopeTerm P r n κ)
    (f g : prismPolynomialCompletion P (Fin r) →+* Y.X.B ⧸ Y.X.Q.ideal)
    (h : f.comp (prismPolynomialUnit P (Fin r)) = g.comp (prismPolynomialUnit P (Fin r))) :
    f = g := by
  let B := MvPolynomial (Fin r) (A ⧸ P.ideal)
  let D := Y.X.B ⧸ Y.X.Q.ideal
  let k : B →+* D := g.comp (prismPolynomialUnit P (Fin r))
  let := k.toAlgebra
  have hD : IsModuleComplete B (p : B) (ModuleCat.of B D) := by
    apply (isModuleComplete_algebraMap_iff B D (p : B) D).mp
    change IsModuleComplete D (k (p : B)) (ModuleCat.of D D)
    rw [map_natCast]
    exact isModuleComplete_principal_quotient_natCast Y.X.B p Y.X.Q.generator Y.X.Q.complete_p
  obtain ⟨_, _, hu⟩ := principalCompletion_existsUnique_ringHom B (p : B) D k hD
  exact (hu f h).trans (hu g rfl).symm

private theorem affineTermMap_sec (U : AffineEnvelopeTerm P r m κ)
    (Y : AffineEnvelopeTerm P r n κ) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (h : OrientedPrism.Hom U.X.Q Y.X.Q) (hb : h.comp U.X.toHom = Y.X.toHom)
    (hX : ∀ j i, h.toRingHom (U.η (affineVariable P r m j i)) =
        Y.η (affineVariable P r n j (θ.toOrderHom i))) :
    h.quotientMap.comp U.X.sec = Y.X.sec := by
  apply affineTerm_sec_ext P Y
  apply MvPolynomial.ringHom_ext'
  · rw [RingHom.comp_assoc, RingHom.comp_assoc]
    change (h.quotientMap.comp U.X.sec).comp (algebraMap (A ⧸ P.ideal) _) =
      Y.X.sec.comp (algebraMap (A ⧸ P.ideal) _)
    rw [RingHom.comp_assoc, U.X.sec_comp, Y.X.sec_comp, ← OrientedPrism.Hom.quotientMap_comp, hb]
  · intro j
    simp only [RingHom.comp_apply, U.sec_X, Y.sec_X, OrientedPrism.Hom.quotientMap_mk, hX]
    exact Ideal.Quotient.eq.mpr (affineTerm_difference_mem P Y j (θ.toOrderHom 0) 0)

private theorem affineTerm_existsUnique_map (U : AffineEnvelopeTerm P r m κ)
    (Y : AffineEnvelopeTerm P r n κ) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    ∃! f : U.X ⟶ Y.X, ∀ j i,
      f.toHom.toRingHom (U.η (affineVariable P r m j i)) =
        Y.η (affineVariable P r n j (θ.toOrderHom i)) := by
  obtain ⟨g, hg, hgu⟩ := affineTerm_existsUnique_eval P Y θ
  have hbase : P.ideal ≤ Y.X.Q.ideal.comap (g.comp (completedFreeDeltaBase P _)) := by
    rw [hg.2.1]
    exact Y.X.toHom.ideal_le
  have hI : (affineDifferenceIdeal P r m).map g ≤ Y.X.Q.ideal := by
    rw [Ideal.map_le_iff_le_comap, affineDifferenceIdeal, Ideal.span_le]
    rintro x (hx | ⟨⟨j, i⟩, rfl⟩)
    · change x = completedFreeDeltaBase P _ P.generator at hx
      subst x
      change (g.comp (completedFreeDeltaBase P _)) P.generator ∈ Y.X.Q.ideal
      rw [hg.2.1]
      exact Y.X.toHom.map_generator_mem
    · change g (affineVariable P r m j i - affineVariable P r m j 0) ∈ Y.X.Q.ideal
      rw [map_sub, hg.2.2, hg.2.2]
      exact affineTerm_difference_mem P Y j _ _
  obtain ⟨h, hh, huniq⟩ := U.envelope.lift Y.X.Q g hg.1 hbase hI
  have hgen : h (U.η (completedFreeDeltaBase P _ P.generator)) ∈ Y.X.Q.ideal := by
    change (h.comp U.η) (completedFreeDeltaBase P _ P.generator) ∈ Y.X.Q.ideal
    rw [hh.2]
    exact hbase (Ideal.subset_span rfl)
  let f : OrientedPrism.Hom U.X.Q Y.X.Q := ⟨h, hh.1, by
    rw [U.envelope.ideal_eq, Ideal.span_le]
    rintro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact hgen⟩
  have hf : f.comp U.X.toHom = Y.X.toHom := by
    apply OrientedPrism.Hom.ext
    change h.comp U.X.toHom.toRingHom = Y.X.toHom.toRingHom
    rw [← U.base_eq, ← RingHom.comp_assoc, hh.2, hg.2.1]
  have hfX (j : Fin r) (i : Fin (m+1)) :
      f.toRingHom (U.η (affineVariable P r m j i)) =
        Y.η (affineVariable P r n j (θ.toOrderHom i)) := by
    change (h.comp U.η) (affineVariable P r m j i) = _
    rw [hh.2, hg.2.2]
  refine ⟨⟨f, hf, affineTermMap_sec P U Y θ f hf hfX⟩, hfX, ?_⟩
  intro f' hf'X
  apply PrismOver.Hom.ext
  apply OrientedPrism.Hom.ext
  apply huniq
  refine ⟨f'.toHom.map_delta, ?_⟩
  have ht : ∀ (k : completedFreeDelta P (AffineIndex.{u} r m) →+* Y.X.B),
      ((completedFreeDeltaStructure P _).IsDeltaHom Y.X.Q.deltaStructure k ∧
        k.comp (completedFreeDeltaBase P _) = Y.X.toHom.toRingHom ∧
        ∀ j i, k (affineVariable P r m j i) =
          Y.η (affineVariable P r n j (θ.toOrderHom i))) → k = g := hgu
  apply ht
  refine ⟨f'.toHom.map_delta.comp U.envelope.isDeltaHom, ?_, hf'X⟩
  rw [RingHom.comp_assoc, U.base_eq]
  exact congrArg OrientedPrism.Hom.toRingHom f'.comm_base

/-- 頂点の添字を θ で写す一意の envelope 射。 -/
def affineTermMap (U : AffineEnvelopeTerm P r m κ)
    (Y : AffineEnvelopeTerm P r n κ) (θ : ⦋m⦌ ⟶ ⦋n⦌) : U.X ⟶ Y.X :=
  (affineTerm_existsUnique_map P U Y θ).choose

/-- 構造射は指定された頂点の初期座標に写す。 -/
theorem affineTermMap_apply (U : AffineEnvelopeTerm P r m κ)
    (Y : AffineEnvelopeTerm P r n κ) (θ : ⦋m⦌ ⟶ ⦋n⦌) (j : Fin r) (i : Fin (m+1)) :
    (affineTermMap P U Y θ).toHom.toRingHom (U.η (affineVariable P r m j i)) =
      Y.η (affineVariable P r n j (θ.toOrderHom i)) :=
  (affineTerm_existsUnique_map P U Y θ).choose_spec.1 j i

/-- affine envelope の射は指定された初期座標の像で決まる。 -/
theorem affineTermMap_unique (U : AffineEnvelopeTerm P r m κ)
    (Y : AffineEnvelopeTerm P r n κ) (θ : ⦋m⦌ ⟶ ⦋n⦌) (f : U.X ⟶ Y.X)
    (hf : ∀ j i, f.toHom.toRingHom (U.η (affineVariable P r m j i)) =
      Y.η (affineVariable P r n j (θ.toOrderHom i))) : f = affineTermMap P U Y θ :=
  (affineTerm_existsUnique_map P U Y θ).choose_spec.2 f hf

/-- affine envelope の次数ごとの選択から余単体的な模型を作る。 -/
def cechAlexanderOfAffineTerms (U : ∀ n, AffineEnvelopeTerm P r n κ) :
    CosimplicialObject (PrismOver P (prismPolynomialCompletion P (Fin r)) κ) where
  obj n := (U n.len).X
  map {m n} θ := affineTermMap P (U m.len) (U n.len) θ
  map_id n := by
    symm
    apply affineTermMap_unique
    intro j i
    rfl
  map_comp {l m n} f g := by
    symm
    apply affineTermMap_unique
    intro j i
    change (affineTermMap P (U m.len) (U n.len) g).toHom.toRingHom
      ((affineTermMap P (U l.len) (U m.len) f).toHom.toRingHom
        ((U l.len).η (affineVariable P r l.len j i))) = _
    rw [affineTermMap_apply, affineTermMap_apply]
    rfl

/-- affine envelope の各項から、基底上の余単体的可換代数を作る。 -/
def polyCosimplicialAlgebraOfAffineTerms (U : ∀ n, AffineEnvelopeTerm P r n κ) :
    SerrePositivity.Cosimplicial.CosimplicialAlgebra A :=
  cechAlexanderOfAffineTerms P U ⋙ prismSiteAlgebras P _ κ

end SerrePositivity.BhattScholze.Prismatic
