module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.BigCechAffineEnvelope
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechAlexander
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.BigCechAffineEnvelope
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.Site.PrismOver

/-!
# 小さい affine 模型から大きい prismatic 枠への写像

## 概要
有限個の多項式変数を、完備多項式環の元として大きい枠に入れる。

## 方針
剰余環への写像で各頂点の評価が一致することを用い、小さい枠の包の普遍性を適用する。

## 規約
枠の写像は余単体的可換代数の射。

## 使われ方
BS 著者版 Remark 4.19 と Theorem 6.4 の有限枠から大きい枠への比較。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}

local notation "C" => (A ⧸ P.ideal)

namespace BigCechTerm

variable {Q : Poly (A ⧸ P.ideal)} {n : ℕ} (E : BigCechTerm P Q n)

private theorem eval_surjective (Q : Poly C) (n : ℕ) : Function.Surjective (bigCechEval Q n) := by
  intro q
  exact ⟨MvPolynomial.X (q, 0), MvPolynomial.eval₂Hom_X' _ _ _⟩

private def unitMod : MvPolynomial (BigCechIndex P Q n) A →+* E.carrier ⧸ E.prism.ideal :=
  (Ideal.Quotient.mk E.prism.ideal).comp (E.unit.comp (bigCechInitial P Q n))

private theorem ker_le_unitMod : RingHom.ker (bigCechEval Q n) ≤ RingHom.ker E.unitMod := by
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact E.isEnvelope.map_le (Ideal.mem_map_of_mem E.unit (Ideal.mem_map_of_mem _ hx))

/-- 大きい枠の評価を包の剰余環に降ろした構造射。 -/
def residueSection : polyCompletion P Q.n →+* E.carrier ⧸ E.prism.ideal :=
  (bigCechEval Q n).liftOfSurjective (eval_surjective Q n) ⟨E.unitMod, E.ker_le_unitMod⟩

theorem residueSection_variable (s : BigCechIndex P Q n) :
    E.residueSection s.1 = Ideal.Quotient.mk E.prism.ideal (E.variableImage s) := by
  have h : E.residueSection.comp (bigCechEval Q n) = E.unitMod :=
    RingHom.liftOfSurjective_comp _ _ _
  have hx := RingHom.congr_fun h (MvPolynomial.X s)
  change E.residueSection (bigCechEval Q n (MvPolynomial.X s)) =
    Ideal.Quotient.mk E.prism.ideal (E.unit (bigCechInitial P Q n (MvPolynomial.X s))) at hx
  rwa [bigCechEval, MvPolynomial.eval₂Hom_X', bigCechInitial_X] at hx

end BigCechTerm

variable {Q : Poly (A ⧸ P.ideal)} {m n : ℕ} {κ : Cardinal.{u}}

private def bigIndex (j : Fin Q.n) (i : Fin (n + 1)) : BigCechIndex P Q n :=
  (prismPolynomialUnit P (Fin Q.n) (MvPolynomial.X j), i)

private theorem affineToBig_existsUnique
    (X : AffineEnvelopeTerm P Q.n n κ) (Y : BigCechTerm P Q n) :
    ∃! f : X.X.B →+* Y.carrier,
      X.X.Q.deltaStructure.IsDeltaHom Y.prism.deltaStructure f ∧
      f.comp X.X.toHom.toRingHom = Y.base.toRingHom ∧
      ∀ j i, f (X.η (affineVariable P Q.n n j i)) = Y.variableImage (bigIndex j i) := by
  let S := AffineIndex.{u} Q.n n
  let v (s : S) := Y.variableImage (bigIndex s.down.1 s.down.2)
  obtain ⟨g, hg, huniq⟩ := existsUnique_completedFreeDeltaHom P S
    Y.prism.deltaStructure Y.base.toRingHom Y.base.map_delta Y.prism.complete_p
    Y.base.isModuleComplete_map_generator v
  have hbase : P.ideal ≤ Y.prism.ideal.comap (g.comp (completedFreeDeltaBase P S)) := by
    rw [hg.2.1]
    exact Y.base.ideal_le
  have hI : (affineDifferenceIdeal P Q.n n).map g ≤ Y.prism.ideal := by
    rw [Ideal.map_le_iff_le_comap, affineDifferenceIdeal, Ideal.span_le]
    rintro a (ha | ⟨⟨j, i⟩, rfl⟩)
    · obtain rfl := ha
      change (g.comp (completedFreeDeltaBase P S)) P.generator ∈ Y.prism.ideal
      exact hbase (Ideal.subset_span (Set.mem_singleton _))
    · change g (affineVariable P Q.n n j i - affineVariable P Q.n n j 0) ∈ Y.prism.ideal
      rw [map_sub, affineVariable_eq, affineVariable_eq, hg.2.2, hg.2.2]
      change Y.variableImage (bigIndex j i) - Y.variableImage (bigIndex j 0) ∈ Y.prism.ideal
      exact Ideal.Quotient.eq.mp
        ((Y.residueSection_variable (bigIndex j i)).symm.trans
          (Y.residueSection_variable (bigIndex j 0)))
  obtain ⟨f, hf, hu⟩ := X.envelope.lift Y.prism g hg.1 hbase hI
  refine ⟨f, ⟨hf.1, ?_, ?_⟩, ?_⟩
  · rw [← X.base_eq, ← RingHom.comp_assoc, hf.2, hg.2.1]
  · intro j i
    change (f.comp X.η) (affineVariable P Q.n n j i) = _
    rw [hf.2, affineVariable_eq, hg.2.2]
  · intro l hl
    apply hu
    refine ⟨hl.1, ?_⟩
    apply huniq
    refine ⟨hl.1.comp X.envelope.isDeltaHom, ?_, ?_⟩
    · rw [RingHom.comp_assoc, X.base_eq, hl.2.1]
    · rintro ⟨⟨j, i⟩⟩
      exact hl.2.2 j i

/-- 各次数での有限 affine 枠から大きい枠への環射。 -/
def affineToBig (X : AffineEnvelopeTerm P Q.n n κ) (Y : BigCechTerm P Q n) :
    X.X.B →+* Y.carrier := (affineToBig_existsUnique X Y).choose

private theorem affineToBig_spec (X : AffineEnvelopeTerm P Q.n n κ) (Y : BigCechTerm P Q n) :
    X.X.Q.deltaStructure.IsDeltaHom Y.prism.deltaStructure (affineToBig X Y) ∧
      (affineToBig X Y).comp X.X.toHom.toRingHom = Y.base.toRingHom ∧
      ∀ j i, affineToBig X Y (X.η (affineVariable P Q.n n j i)) = Y.variableImage (bigIndex j i) :=
  (affineToBig_existsUnique X Y).choose_spec.1

private theorem affineToBig_naturality {Q : Poly (A ⧸ P.ideal)}
    (X : ∀ n, AffineEnvelopeTerm P Q.n n κ) (Y : ∀ n, BigCechTerm P Q n)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    (affineToBig (X n.len) (Y n.len)).comp
      (affineTermMap P (X m.len) (X n.len) θ).toHom.toRingHom =
    ((Y m.len).map (Y n.len) (𝟙 Q) θ.toOrderHom).comp
      (affineToBig (X m.len) (Y m.len)) := by
  let x := affineTermMap P (X m.len) (X n.len) θ
  let y := (Y m.len).map (Y n.len) (𝟙 Q) θ.toOrderHom
  let L := (affineToBig (X n.len) (Y n.len)).comp x.toHom.toRingHom
  let R := y.comp (affineToBig (X m.len) (Y m.len))
  have hLδ := (affineToBig_spec (X n.len) (Y n.len)).1.comp x.toHom.map_delta
  have hRδ := ((Y m.len).map_isDeltaHom (Y n.len) (𝟙 Q) θ.toOrderHom).comp
    (affineToBig_spec (X m.len) (Y m.len)).1
  have hLb : L.comp (X m.len).X.toHom.toRingHom = (Y n.len).base.toRingHom := by
    have hx := congrArg OrientedPrism.Hom.toRingHom x.comm_base
    change x.toHom.toRingHom.comp (X m.len).X.toHom.toRingHom = _ at hx
    unfold L
    rw [RingHom.comp_assoc, hx, (affineToBig_spec (X n.len) (Y n.len)).2.1]
  have hRb : R.comp (X m.len).X.toHom.toRingHom = (Y n.len).base.toRingHom := by
    unfold R
    rw [RingHom.comp_assoc, (affineToBig_spec (X m.len) (Y m.len)).2.1,
      (Y m.len).map_base]
  have hLX (j : Fin Q.n) (i : Fin (m.len + 1)) :
      L ((X m.len).η (affineVariable P Q.n m.len j i)) =
        (Y n.len).variableImage (bigIndex j (θ.toOrderHom i)) := by
    change affineToBig (X n.len) (Y n.len)
      ((affineTermMap P (X m.len) (X n.len) θ).toHom.toRingHom
        ((X m.len).η (affineVariable P Q.n m.len j i))) = _
    rw [affineTermMap_apply, (affineToBig_spec (X n.len) (Y n.len)).2.2]
  have hRX (j : Fin Q.n) (i : Fin (m.len + 1)) :
      R ((X m.len).η (affineVariable P Q.n m.len j i)) =
        (Y n.len).variableImage (bigIndex j (θ.toOrderHom i)) := by
    change y (affineToBig (X m.len) (Y m.len)
      ((X m.len).η (affineVariable P Q.n m.len j i))) = _
    rw [(affineToBig_spec (X m.len) (Y m.len)).2.2]
    unfold y
    rw [BigCechTerm.map_variableImage]
    simp only [BigCechTerm.indexMap, bigIndex, polyCompletionMap_id, AlgHom.id_apply]
  let u := (X m.len).η
  have hLu :
      (completedFreeDeltaStructure P _).IsDeltaHom (Y n.len).prism.deltaStructure (L.comp u) :=
    hLδ.comp (X m.len).envelope.isDeltaHom
  have hRu :
      (completedFreeDeltaStructure P _).IsDeltaHom (Y n.len).prism.deltaStructure (R.comp u) :=
    hRδ.comp (X m.len).envelope.isDeltaHom
  have hbaseL : (L.comp u).comp (completedFreeDeltaBase P _) = (Y n.len).base.toRingHom := by
    rw [RingHom.comp_assoc, show u.comp (completedFreeDeltaBase P _) =
      (X m.len).X.toHom.toRingHom from (X m.len).base_eq, hLb]
  have hbaseR : (R.comp u).comp (completedFreeDeltaBase P _) = (Y n.len).base.toRingHom := by
    rw [RingHom.comp_assoc, show u.comp (completedFreeDeltaBase P _) =
      (X m.len).X.toHom.toRingHom from (X m.len).base_eq, hRb]
  have hI : (affineDifferenceIdeal P Q.n m.len).map (L.comp u) ≤ (Y n.len).prism.ideal := by
    rw [← Ideal.map_map]
    apply (Ideal.map_mono (X m.len).envelope.map_le).trans
    rw [(X m.len).envelope.ideal_eq, Ideal.map_span, Set.image_singleton]
    apply Ideal.span_le.mpr
    rw [Set.singleton_subset_iff]
    change ((L.comp u).comp (completedFreeDeltaBase P _)) P.generator ∈ _
    rw [hbaseL]
    exact (Y n.len).base.map_generator_mem
  obtain ⟨k, _, huniq⟩ := (X m.len).envelope.lift (Y n.len).prism (L.comp u) hLu
    (by rw [hbaseL]; exact (Y n.len).base.ideal_le) hI
  have h := completedFreeDeltaHom_ext P _ (Y n.len).prism.deltaStructure
    (Y n.len).base.toRingHom (Y n.len).base.map_delta (Y n.len).prism.complete_p
    (Y n.len).base.isModuleComplete_map_generator hLu hRu hbaseL hbaseR
    (by
      rintro ⟨⟨j, i⟩⟩
      exact (hLX j i).trans (hRX j i).symm)
  exact (huniq L ⟨hLδ, rfl⟩).trans (huniq R ⟨hRδ, h.symm⟩).symm

/-- 有限 affine 模型から大きい枠への余単体的代数の射。 -/
def cechAlexanderFrame (Q : Poly C) (X : ∀ n, AffineEnvelopeTerm P Q.n n κ)
    (Y : ∀ (Q' : Poly C) n, BigCechTerm P Q' n) :
    polyCosimplicialAlgebraOfAffineTerms P X ⟶ (bigCechAlexanderOfTerms P Y).obj Q where
  app n := Under.homMk (CommRingCat.ofHom (affineToBig (X n.len) (Y Q n.len)))
    (CommRingCat.hom_ext ((affineToBig_spec (X n.len) (Y Q n.len)).2.1))
  naturality {m n} θ := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    exact affineToBig_naturality X (Y Q) θ

/-- 有界 prism 上の小さい affine 模型から大きい affine 模型への標準射。 -/
def affineCechAlexanderFrame (hP : IsBoundedPrism P) (Q : Poly C) :
    polyCosimplicialAlgebra P hP Q.n ⟶ (bigCechAlexander P hP).obj Q := by
  unfold polyCosimplicialAlgebra bigCechAlexander
  exact cechAlexanderFrame Q (fun n => affineEnvelopeTerm P hP Q.n n (polyCutoff P Q.n) le_rfl)
    (fun Q n => affineBigCechTerm P Q n hP)

end SerrePositivity.BhattScholze.Prismatic
