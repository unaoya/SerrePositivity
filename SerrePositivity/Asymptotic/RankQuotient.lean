module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CategoryTheory.HomotopyProperty
public import SerrePositivity.Asymptotic.SequenceComplex
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import SerrePositivity.Asymptotic.FreeSequence
public import Mathlib.CategoryTheory.Localization.Linear
public import SerrePositivity.CategoryTheory.Triangulated.VerdierLift
public import SerrePositivity.PerfectComplex.ResolutionFamilies
public import Mathlib.LinearAlgebra.StdBasis
public import SerrePositivity.CategoryTheory.ScalarSupport

/-! # 小さいランクの複体による Verdier 商

## 概要

共通有界な自由列のホモトピー圏を、各次数のランクが o(s) の複体で割った Verdier 商 `SequenceRankQuotient` を作り、係数変更の降下、スカラー作用、自由複体の族の組み戻し（`AssembleComplex`）、長さ O(s) の有限長加群列の自由列による分解、台と共通の零ホモトピー、台を持つ部分圏のランク商から全体の商への完全忠実性を与える。

## 方針

ランク条件がシフトと錐で保たれることから Verdier 局所化を作る。完全忠実性はスカラーの錐を反復する因子化定理による。

## 規約

冪等完備化より前の商を扱う。台の条件に必要なのは消去指数の一様性で、ホモトピーの係数の有界性ではない。

## 使われ方

Asymptotic の残り、Paper/Section4。
-/

@[expose] public noncomputable section

universe u

section RankQuotientPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Filter Asymptotics
open scoped ZeroObject

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}

namespace FreeSequence

/-- 自由列の同型は、各段のランクを保つ。 -/
lemma rank_eq_of_iso {X Y : FreeSequence R s} (e : X ≅ Y) (n : ℕ) :
    X.rank n = Y.rank n := by
  have h := ((evaluation n).mapIso e).toLinearEquiv.finrank_eq
  change Module.finrank R (Fin (X.rank n) → R) =
    Module.finrank R (Fin (Y.rank n) → R) at h
  simpa only [Module.finrank_fin_fun] using h

/-- 零対象の各段のランクは零である。 -/
lemma rank_eq_zero_of_isZero (X : FreeSequence R s) (hX : IsZero X) (n : ℕ) :
    X.rank n = 0 :=
  rank_eq_of_iso (hX.iso zero_isZero) n

/-- 二項直和のランクは各段で加法的である。 -/
lemma rank_biprod (X Y : FreeSequence R s) (n : ℕ) :
    (X ⊞ Y).rank n = X.rank n + Y.rank n := by
  exact rank_eq_of_iso (IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X Y)
    (isBinaryBilimitOfTotal (sumBicone X Y) (sumBicone_total X Y)).isLimit) n

/-- 任意の有限自由加群列は、ランク条件を満たす標準自由列で各段同型に表せる。 -/
lemma exists_model (M : ℕ → ModuleCat.{u} R)
    [∀ n, Module.Free R (M n)] [∀ n, Module.Finite R (M n)]
    (hM : (fun n ↦ (Module.finrank R (M n) : ℝ)) =O[atTop] (fun n ↦ (s n : ℝ))) :
    ∃ X : FreeSequence R s, ∀ n, Nonempty ((evaluation n).obj X ≅ M n) :=
  ⟨⟨fun n ↦ Module.finrank R (M n), hM⟩,
    fun n ↦ ⟨(Module.finBasis R (M n)).equivFun.symm.toModuleIso⟩⟩

end FreeSequence

/-- 共通有界で、各次数のランク列が通常の `o(s)` であるという条件。 -/
def rankSmallComplex : ObjectProperty (CochainComplex (FreeSequence R s) ℤ) :=
  fun K ↦ strictlyBoundedComplex (FreeSequence R s) K ∧
    ∀ i, (fun n ↦ ((K.X i).rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ))

/-- ランクが小さい代表複体をもつホモトピー圏の対象。 -/
def rankSmallHomotopy : ObjectProperty (HomotopyCategory (FreeSequence R s) (.up ℤ)) :=
  rankSmallComplex.strictMap (HomotopyCategory.quotient _ _)

omit [Nontrivial R] in
/-- ランク条件はホモトピー圏の代表複体について読める。 -/
@[simp] lemma rankSmallHomotopy_quotient (K : CochainComplex (FreeSequence R s) ℤ) :
    rankSmallHomotopy ((HomotopyCategory.quotient _ _).obj K) ↔ rankSmallComplex K :=
  homotopyProperty_strictMap_quotient rankSmallComplex K

instance : (rankSmallHomotopy (R := R) (s := s)).ContainsZero where
  exists_zero := ⟨(HomotopyCategory.quotient _ _).obj 0,
    Functor.map_isZero _ (isZero_zero _), by
      rw [rankSmallHomotopy_quotient]
      refine ⟨⟨0, 0, inferInstance, inferInstance⟩, ?_⟩
      intro i
      have hz (n : ℕ) : (((0 : CochainComplex (FreeSequence R s) ℤ).X i).rank n) = 0 :=
        FreeSequence.rank_eq_zero_of_isZero _
          ((HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)) n
      simpa only [hz, Nat.cast_zero] using (isLittleO_zero (fun n ↦ (s n : ℝ)) atTop)⟩

instance : (rankSmallHomotopy (R := R) (s := s)).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        rw [rankSmallHomotopy_quotient] at hK
        rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj,
          rankSmallHomotopy_quotient]
        refine ⟨?_, fun i ↦ hK.2 (i + n)⟩
        exact strictlyBoundedComplex_shift _ hK.1 n }

/-- 小さいランクの複体の間の射の錐も、各次数で小さいランクをもつ。 -/
lemma rankSmallComplex_mappingCone {K L : CochainComplex (FreeSequence R s) ℤ}
    (f : K ⟶ L) (hK : rankSmallComplex K) (hL : rankSmallComplex L) :
    rankSmallComplex (CochainComplex.mappingCone f) := by
  refine ⟨strictlyBoundedComplex_mappingCone _ f hK.1 hL.1, fun i ↦ ?_⟩
  have he := HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) (by simp)
  have hr (n : ℕ) := FreeSequence.rank_eq_of_iso he n
  simp only [FreeSequence.rank_biprod] at hr
  simp_rw [show ∀ n, ((CochainComplex.mappingCone f).X i).rank n =
    (K.X (i + 1)).rank n + (L.X i).rank n from hr, Nat.cast_add]
  exact (hK.2 (i + 1)).add (hL.2 i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : (rankSmallHomotopy (R := R) (s := s)).IsTriangulatedClosed₃ :=
  homotopyProperty_isTriangulatedClosed₃ _ _ (rankSmallHomotopy_quotient)
    (fun f => rankSmallComplex_mappingCone f)

instance : (rankSmallHomotopy (R := R) (s := s)).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- 共通有界ホモトピー圏における小さいランクの三角部分圏。 -/
def rankSmallBounded : ObjectProperty (SequenceHomotopy R s) :=
  rankSmallHomotopy.isoClosure.inverseImage (boundedHomotopyInclusion _)

instance : (rankSmallBounded (R := R) (s := s)).IsClosedUnderIsomorphisms :=
  inferInstanceAs (rankSmallHomotopy.isoClosure.inverseImage
    (boundedHomotopyInclusion _)).IsClosedUnderIsomorphisms

instance : (rankSmallBounded (R := R) (s := s)).IsTriangulated :=
  inferInstanceAs
    (rankSmallHomotopy.isoClosure.inverseImage (boundedHomotopyInclusion _)).IsTriangulated

/-- 冪等完備化に先立つ、共通有界な自由列のランク商。 -/
abbrev SequenceRankQuotient (R : Type u) [CommRing R] [Nontrivial R] (s : ℕ → ℕ) :=
  (rankSmallBounded (R := R) (s := s)).trW.Localization

/-- 小さいランクの対象を消す標準的な Verdier 商関手。 -/
abbrev sequenceRankQuotientFunctor : SequenceHomotopy R s ⥤ SequenceRankQuotient R s :=
  (rankSmallBounded (R := R) (s := s)).trW.Q

/-- 小さいランクの有界対象は、構成した Verdier 商で零になる。 -/
lemma sequenceRankQuotient_isZero (X : SequenceHomotopy R s) (hX : rankSmallBounded X) :
    IsZero (sequenceRankQuotientFunctor.obj X) := by
  let P := rankSmallBounded (R := R) (s := s)
  have hf : P.trW (0 : (0 : SequenceHomotopy R s) ⟶ X) :=
    ⟨X, 𝟙 X, 0, contractible_distinguished₁ X, hX⟩
  have := Localization.inverts P.trW.Q P.trW _ hf
  exact IsZero.of_iso (P.trW.Q.map_isZero (isZero_zero _))
    (asIso (P.trW.Q.map (0 : (0 : SequenceHomotopy R s) ⟶ X))).symm

/-- 小さいランクの複体を有界ホモトピー圏に入れると、そのランク商での像は零になる。 -/
lemma sequenceRankQuotient_smallComplex_isZero
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : rankSmallComplex K) :
    IsZero (sequenceRankQuotientFunctor.obj
      ⟨(HomotopyCategory.quotient _ _).obj K,
        (boundedHomotopyProperty_quotient _ K).2 hK.1⟩) := by
  apply sequenceRankQuotient_isZero
  exact ⟨(HomotopyCategory.quotient _ _).obj K,
    (rankSmallHomotopy_quotient K).2 hK, ⟨Iso.refl _⟩⟩

end SerrePositivity.Asymptotic

end RankQuotientPart

section RankQuotientBaseChangePart

namespace SerrePositivity.Asymptotic

open CategoryTheory

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S)

omit [Nontrivial R] [Nontrivial S] in
/-- 小さいランクの共通有界複体は係数変更で保たれる。 -/
lemma changeRing_rankSmallComplex (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : rankSmallComplex K) :
    rankSmallComplex (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K) := by
  refine ⟨?_, hK.2⟩
  obtain ⟨a, b, ha, hb⟩ := hK.1
  exact ⟨a, b, inferInstanceAs (CochainComplex.IsStrictlyGE
    (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K) a),
    inferInstanceAs (CochainComplex.IsStrictlyLE
      (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K) b)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [Nontrivial R] [Nontrivial S] in
/-- 小さいランクの代表をもつ有界ホモトピー対象は、係数変更後も同じ性質をもつ。 -/
lemma changeRing_rankSmallBounded (X : SequenceHomotopy R s) (hX : rankSmallBounded X) :
    rankSmallBounded ((mapBoundedHomotopy (FreeSequence.changeRing φ)).obj X) := by
  obtain ⟨Y, hY, ⟨e⟩⟩ := hX
  obtain ⟨K, hK⟩ := hY
  refine ⟨_, (rankSmallHomotopy_quotient _).2 (changeRing_rankSmallComplex φ K hK),
    ⟨((FreeSequence.changeRing φ).mapHomotopyCategory (.up ℤ)).mapIso e⟩⟩

omit [Nontrivial R] in
/-- ランク商への係数変更は、元のランク商の分母を可逆にする。 -/
lemma changeRing_inverts_rankSmall :
    (rankSmallBounded (R := R) (s := s)).trW.IsInvertedBy
      (mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ sequenceRankQuotientFunctor) := by
  let F := mapBoundedHomotopy (FreeSequence.changeRing (s := s) φ)
  let P := rankSmallBounded (R := S) (s := s)
  have h : rankSmallBounded (R := R) (s := s) ≤ P.inverseImage F :=
    fun X hX ↦ changeRing_rankSmallBounded φ X hX
  intro X Y f hf
  exact P.inverseImage_trW_isInverted F P.trW.Q f
    (ObjectProperty.trW_monotone h f hf)

/-- 冪等完備化前のランク商に誘導される係数変更関手。 -/
@[implicit_reducible]
noncomputable def rankQuotientChangeRing : SequenceRankQuotient R s ⥤ SequenceRankQuotient S s :=
  Localization.lift
    (mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ sequenceRankQuotientFunctor)
    (changeRing_inverts_rankSmall φ) sequenceRankQuotientFunctor

/-- 係数変更を商に降ろす操作は、標準商関手と自然同型を介して可換である。 -/
noncomputable def rankQuotientChangeRing_fac :
    sequenceRankQuotientFunctor ⋙ rankQuotientChangeRing (s := s) φ ≅
      mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ sequenceRankQuotientFunctor :=
  Localization.fac _ (changeRing_inverts_rankSmall φ) _

noncomputable instance : Localization.Lifting
    (sequenceRankQuotientFunctor (R := R) (s := s)) (rankSmallBounded (R := R) (s := s)).trW
    (mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ sequenceRankQuotientFunctor)
    (rankQuotientChangeRing φ) :=
  ⟨rankQuotientChangeRing_fac φ⟩

noncomputable instance : (rankQuotientChangeRing (s := s) φ).CommShift ℤ :=
  Functor.commShiftOfLocalization sequenceRankQuotientFunctor
    (rankSmallBounded (R := R) (s := s)).trW ℤ
    (mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ sequenceRankQuotientFunctor)
    (rankQuotientChangeRing φ)

instance : NatTrans.CommShift (rankQuotientChangeRing_fac (s := s) φ).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization
    (sequenceRankQuotientFunctor (R := R) (s := s)) (rankSmallBounded (R := R) (s := s)).trW ℤ
    (mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ sequenceRankQuotientFunctor)
    (rankQuotientChangeRing φ)

/-- ランク商に降ろした係数変更は三角関手である。 -/
instance : (rankQuotientChangeRing (s := s) φ).IsTriangulated := by
  let := Localization.essSurj_mapArrow
    (sequenceRankQuotientFunctor (R := R) (s := s)) (rankSmallBounded (R := R) (s := s)).trW
  exact Functor.isTriangulated_of_precomp_iso (rankQuotientChangeRing_fac φ)

end SerrePositivity.Asymptotic

end RankQuotientBaseChangePart

section SequenceLinearPart

namespace SerrePositivity.Asymptotic.FreeSequence

open CategoryTheory

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 射のスカラー倍は段ごとの線形写像のスカラー倍である。 -/
instance : Linear R (FreeSequence R s) where
  homModule X Y := inferInstanceAs
    (Module R (∀ n, (Fin (X.rank n) → R) →ₗ[R] (Fin (Y.rank n) → R)))
  smul_comp _ _ _ a f g := by
    funext n
    exact LinearMap.comp_smul _ _ _
  comp_smul _ _ _ f a g := by
    funext n
    rfl

instance (n : ℕ) : (evaluation (R := R) (s := s) n).Linear R where
  map_smul := by intros; rfl

end SerrePositivity.Asymptotic.FreeSequence

end SequenceLinearPart

section AssembleComplexPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter Asymptotics

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}
  (P : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (r : ℤ → ℕ → ℕ)
  (hr : ∀ i, (fun n ↦ (r i n : ℝ)) =O[atTop] (fun n ↦ (s n : ℝ)))
  (e : ∀ n i, ModuleCat.of R (Fin (r i n) → R) ≅ (P n).X i)

/-- 指定された基底の同型で微分を移して、自由列の複体を作る。 -/
def assembleComplex : CochainComplex (FreeSequence R s) ℤ where
  X i := ⟨r i, hr i⟩
  d i j n := ((e n i).hom ≫ (P n).d i j ≫ (e n j).inv).hom
  shape i j hij := by
    funext n
    change ((e n i).hom ≫ (P n).d i j ≫ (e n j).inv).hom = 0
    rw [(P n).shape i j hij, zero_comp, comp_zero]
    rfl
  d_comp_d' i j k _ _ := by
    funext n
    have h : ((e n i).hom ≫ (P n).d i j ≫ (e n j).inv) ≫
        ((e n j).hom ≫ (P n).d j k ≫ (e n k).inv) = 0 := by simp
    exact congrArg ModuleCat.Hom.hom h

/-- 組み戻した複体を評価すると、元の複体と鎖同型になる。 -/
def evaluateAssembleIso (n : ℕ) :
    (evaluateComplex n).obj (assembleComplex P r hr e) ≅ P n :=
  HomologicalComplex.Hom.isoOfComponents (e n) (by
    intro i j _
    change (e n i).hom ≫ (P n).d i j =
      ((e n i).hom ≫ (P n).d i j ≫ (e n j).inv) ≫ (e n j).hom
    simp)

/-- 段ごとの共通有界性は、組み戻した自由列の複体の有界性になる。 -/
lemma assembleComplex_bounded (a b : ℤ)
    (hb : ∀ n i, (i < a ∨ b < i) → IsZero ((P n).X i)) :
    strictlyBoundedComplex (FreeSequence R s) (assembleComplex P r hr e) := by
  have hzero (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((assembleComplex P r hr e).X i) := by
    apply (IsZero.iff_id_eq_zero _).2
    funext n
    exact congrArg ModuleCat.Hom.hom
      (((hb n i hi).of_iso (e n i)).eq_of_src
        (𝟙 (ModuleCat.of R (Fin (r i n) → R))) 0)
  exact ⟨a, b, (CochainComplex.isStrictlyGE_iff _ a).2 (fun i hi ↦ hzero i (.inl hi)),
    (CochainComplex.isStrictlyLE_iff _ b).2 (fun i hi ↦ hzero i (.inr hi))⟩

/-- 各項のランクが `o(s)` なら、組み戻した共通有界複体はランク商で消える側に属する。 -/
lemma assembleComplex_rankSmall (a b : ℤ)
    (hb : ∀ n i, (i < a ∨ b < i) → IsZero ((P n).X i))
    (hsmall : ∀ i, (fun n ↦ (r i n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ))) :
    rankSmallComplex (assembleComplex P r hr e) :=
  ⟨assembleComplex_bounded P r hr e a b hb, hsmall⟩

end SerrePositivity.Asymptotic

end AssembleComplexPart

section SequenceResolutionPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits IsLocalRing Filter Asymptotics

variable {A : Type u} [CommRing A] [IsLocalRing A] {s : ℕ → ℕ}

/-- 長さ `O(s)` の有限長加群列は、共通範囲 `[-d,0]` の自由列の複体で分解できる。
ランクは長さと剰余体の固定分解のランクの積である。 -/
theorem exists_sequence_resolution
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
    (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
    (d : ℕ) (hKb : ∀ i, i < -(d : ℤ) → IsZero (K.X i))
    (M : ℕ → ModuleCat.{u} A) (hM : ∀ n, IsFiniteLength A (M n))
    (hbound : (fun n ↦ ((Module.length A (M n)).toNat : ℝ)) =O[atTop]
      (fun n ↦ (s n : ℝ))) :
    ∃ F : CochainComplex (FreeSequence A s) ℤ,
      (F.IsStrictlyGE (-(d : ℤ)) ∧ F.IsStrictlyLE 0) ∧
      (∀ n, Nonempty (IsResolutionOf ((evaluateComplex n).obj F) (M n))) ∧
      ∀ i n, (F.X i).rank n =
        (Module.length A (M n)).toNat * Module.finrank A (K.X i) := by
  obtain ⟨P, hres, hfree, hfinite, hb, hrank⟩ :=
    exists_uniform_free_resolutions K hK hKf hKn d hKb M hM
  let r (i : ℤ) (n : ℕ) := Module.finrank A ((P n).X i)
  have hr (i : ℤ) : (fun n ↦ (r i n : ℝ)) =O[atTop] (fun n ↦ (s n : ℝ)) :=
    resolutionFamily_rank_isBigO K M P hrank _ hbound i
  let e (n : ℕ) (i : ℤ) : ModuleCat.of A (Fin (r i n) → A) ≅ (P n).X i := by
    have := hfree n i
    have := hfinite n i
    exact (Module.finBasis A ((P n).X i)).equivFun.toModuleIso.symm
  let F := assembleComplex P r hr e
  have hzero (i : ℤ) (hi : i < -(d : ℤ) ∨ 0 < i) : IsZero (F.X i) := by
    apply (IsZero.iff_id_eq_zero _).2
    funext n
    exact congrArg ModuleCat.Hom.hom
      (((hb n i hi).of_iso (e n i)).eq_of_src
        (𝟙 (ModuleCat.of A (Fin (r i n) → A))) 0)
  refine ⟨F, ⟨(CochainComplex.isStrictlyGE_iff _ _).2 (fun i hi ↦ hzero i (.inl hi)),
    (CochainComplex.isStrictlyLE_iff _ _).2 (fun i hi ↦ hzero i (.inr hi))⟩,
    ?_, fun i n ↦ hrank n i⟩
  intro n
  let en := evaluateAssembleIso P r hr e n
  let hn := (hres n).some
  refine ⟨{ isZero_X := fun i hi ↦ (hn.isZero_X i hi).of_iso (e n i)
            projective := fun i ↦ ModuleCat.projective_of_free (Pi.basisFun A (Fin (r i n)))
            isZero_homology := fun i hi ↦ (hn.isZero_homology i hi).of_iso
              ((HomologicalComplex.homologyFunctor _ _ i).mapIso en)
            homologyZeroIso :=
              (HomologicalComplex.homologyFunctor _ _ 0).mapIso en ≪≫ hn.homologyZeroIso }⟩

end SerrePositivity.Asymptotic

end SequenceResolutionPart

section SequenceSupportPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 共通有界複体を共通有界ホモトピー圏の対象とみなす。 -/
def sequenceHomotopyObj (F : CochainComplex (FreeSequence R s) ℤ)
    (hF : strictlyBoundedComplex (FreeSequence R s) F) : SequenceHomotopy R s :=
  ⟨(HomotopyCategory.quotient _ _).obj F, (boundedHomotopyProperty_quotient _ F).2 hF⟩

/-- ホモトピー圏でスカラー作用が零であることは、各段で零ホモトピックなことと同値。 -/
lemma sequence_smul_id_zero_iff
    (F : CochainComplex (FreeSequence R s) ℤ)
    (hF : strictlyBoundedComplex (FreeSequence R s) F) (a : R) :
    a • 𝟙 (sequenceHomotopyObj F hF) = 0 ↔
      ∀ n, Nonempty (Homotopy (a • 𝟙 ((evaluateComplex n).obj F)) 0) := by
  have h : a • 𝟙 (sequenceHomotopyObj F hF) = 0 ↔
      (HomotopyCategory.quotient _ _).map (a • 𝟙 F) =
        (HomotopyCategory.quotient _ _).map (0 : F ⟶ F) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero]
    exact ⟨fun h ↦ congrArg (fun f ↦ f.hom) h, fun h ↦ ObjectProperty.hom_ext _ h⟩
  rw [h, quotient_map_eq_iff_pointwise]
  apply forall_congr'
  intro n
  simp only [Functor.map_zero, HomotopyCategory.quotient_map_eq_zero_iff]
  have : (evaluateComplex (R := R) (s := s) n).Linear R := by
    change ((FreeSequence.evaluation (R := R) (s := s) n).mapHomologicalComplex (.up ℤ)).Linear R
    infer_instance
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id]

/-- 台をもつことは、全段に共通の正の指数による零ホモトピーの存在と同値。 -/
lemma sequence_supported_iff {ι : Type*} (z : ι → R)
    (F : CochainComplex (FreeSequence R s) ℤ)
    (hF : strictlyBoundedComplex (FreeSequence R s) F) :
    scalarSupported z (sequenceHomotopyObj F hF) ↔
      ∃ v : ℕ, 0 < v ∧ ∀ j n,
        Nonempty (Homotopy (z j ^ v • 𝟙 ((evaluateComplex n).obj F)) 0) := by
  simp only [scalarSupported, sequence_smul_id_zero_iff]

/-- 共通範囲 `[-d,0]` の分解では、加群列の共通の消去指数から列全体の台が得られる。 -/
lemma sequence_resolution_supported {ι : Type*} (z : ι → R)
    (F : CochainComplex (FreeSequence R s) ℤ) (d : ℕ)
    (ha : F.IsStrictlyGE (-(d : ℤ))) (hb : F.IsStrictlyLE 0)
    (M : ℕ → ModuleCat.{u} R)
    (hres : ∀ n, Nonempty (IsResolutionOf ((evaluateComplex n).obj F) (M n)))
    (N : ℕ) (hN : 0 < N) (hM : ∀ n j, z j ^ N • 𝟙 (M n) = 0) :
    scalarSupported z (sequenceHomotopyObj F ⟨-(d : ℤ), 0, ha, hb⟩) := by
  apply (sequence_supported_iff _ _ _).2
  refine ⟨N * (d + 1), Nat.mul_pos hN (by omega), fun j n ↦ ?_⟩
  apply resolutionFamily_uniform_nullHomotopies M (fun n ↦ (evaluateComplex n).obj F)
    hres d ?_ z N hM n j
  intro n i hi
  rcases hi with hi | hi
  · exact (FreeSequence.evaluation n).map_isZero (F.isZero_of_isStrictlyGE _ i hi)
  · exact (FreeSequence.evaluation n).map_isZero (F.isZero_of_isStrictlyLE _ i hi)

end SerrePositivity.Asymptotic

end SequenceSupportPart

section SupportedRankQuotientPart

namespace SerrePositivity.Asymptotic

open CategoryTheory

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}
  {e : ℕ} (z : Fin e → R)

/-- 商を取る前に共通の冪で台をもつ有界自由列。 -/
abbrev supportedSequence : ObjectProperty (SequenceHomotopy R s) := scalarSupported z

/-- ランク商の中で共通の冪で台をもつ対象。 -/
abbrev supportedRankQuotient : ObjectProperty (SequenceRankQuotient R s) := scalarSupported z

/-- 商の前の支持つき対象は、商に移した後も台をもつ。 -/
lemma supportedSequence_map_quotient (X : SequenceHomotopy R s)
    (hX : supportedSequence z X) :
    supportedRankQuotient z (sequenceRankQuotientFunctor.obj X) :=
  scalarSupported_map z sequenceRankQuotientFunctor X hX

/-- 支持部分圏の中でランクの小さい対象を消す Verdier 商。 -/
abbrev SupportedSequenceRankQuotient :=
  ((rankSmallBounded (R := R) (s := s)).inverseImage (supportedSequence z).ι).trW.Localization

/-- 支持部分圏のランク商から全体のランク商への標準関手。 -/
@[implicit_reducible]
noncomputable def supportedRankQuotientInclusion :
    SupportedSequenceRankQuotient (s := s) z ⥤ SequenceRankQuotient R s :=
  ((supportedSequence z).triangulatedLocalizerMorphism rankSmallBounded).localizedFunctor
    ((rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q)
    sequenceRankQuotientFunctor

noncomputable instance : (supportedRankQuotientInclusion (s := s) z).CommShift ℤ := by
  dsimp only [supportedRankQuotientInclusion]
  infer_instance

/-- 支持部分圏の商からの関手は完全三角形を保存する。 -/
instance : (supportedRankQuotientInclusion (s := s) z).IsTriangulated := by
  let A := supportedSequence (s := s) z
  let B := rankSmallBounded (R := R) (s := s)
  let Φ := A.triangulatedLocalizerMorphism B
  let L := (B.inverseImage A.ι).trW.Q
  let := Localization.essSurj_mapArrow L (B.inverseImage A.ι).trW
  exact Functor.isTriangulated_of_precomp_iso
    (CatCommSq.iso Φ.functor L B.trW.Q (Φ.localizedFunctor L B.trW.Q)).symm

/-- 支持つき小対象を経由する因子化により、商の関手は充満である。 -/
instance : (supportedRankQuotientInclusion (s := s) z).Full := by
  dsimp only [supportedRankQuotientInclusion]
  infer_instance

/-- 同じ因子化により、商の関手は忠実である。 -/
instance : (supportedRankQuotientInclusion (s := s) z).Faithful := by
  dsimp only [supportedRankQuotientInclusion]
  infer_instance

/-- 商で台をもつ対象は、商の前で一様に台をもつ対象の像の直和因子である。 -/
theorem supportedRankQuotient_retract (Y : SequenceRankQuotient R s)
    (hY : supportedRankQuotient z Y) :
    ∃ X : SequenceHomotopy R s, supportedSequence z X ∧
      Nonempty (Retract Y (sequenceRankQuotientFunctor.obj X)) := by
  let := Localization.essSurj (sequenceRankQuotientFunctor (R := R) (s := s))
    (rankSmallBounded (R := R) (s := s)).trW
  exact scalarSupported_retract_image sequenceRankQuotientFunctor z Y hY

end SerrePositivity.Asymptotic

end SupportedRankQuotientPart

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Paper "Lemma 4.2"] _root_.SerrePositivity.Asymptotic.supportedRankQuotientInclusion
