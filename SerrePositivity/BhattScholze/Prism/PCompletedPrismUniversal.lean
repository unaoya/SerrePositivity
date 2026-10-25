module

public import SerrePositivity.BhattScholze.Prism.PCompletedDistinguishedPrism
public import SerrePositivity.BhattScholze.Prism.PCompletedDeltaRecovery
public import SerrePositivity.BhattScholze.Prism.OrientedPrismIsoCriterion
public import Mathlib.RingTheory.AdicCompletion.Topology

/-! # p進完備δ完全化のprismへの標準射と普遍性

distinguished生成元を持つoriented prismについて、生成元像のd進完備性を
明示した普遍性を証明する。既に完全なprismなら、その追加完備性も復元同型から供給する。
一般prismの完全化の存在や導来(p,d)完備化との比較は結論しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

section Universal
variable (P : OrientedPrism p A) (hd : P.deltaStructure.IsDistinguished P.generator)
variable [IsAdicComplete
  (Ideal.span {pCompletedDeltaPerfectionMap P.deltaStructure P.generator})
  (PCompletedDeltaPerfection P.deltaStructure)]

/-- 元のoriented prismから具体的なp進完備δ完全化prismへの標準射。 -/
def pCompletedPrismMap : OrientedPrism.Hom P
    (pCompletedDistinguishedPrism P.deltaStructure P.generator hd) := by
  refine ⟨pCompletedDeltaPerfectionMap P.deltaStructure,
    pCompletedDeltaPerfectionMap_isDeltaHom P.deltaStructure, ?_⟩
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  exact Ideal.subset_span (Set.mem_singleton _)

/-- 任意の完全oriented prismへのprism射は、標準prism射を通じ一意に延長する。 -/
theorem existsUnique_pCompletedPrismHom
    {B : Type v} [CommRing B] (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)
    (f : OrientedPrism.Hom P Q) :
    ∃! g : OrientedPrism.Hom
      (pCompletedDistinguishedPrism P.deltaStructure P.generator hd) Q,
      g.comp (pCompletedPrismMap P hd) = f := by
  obtain ⟨g, hg, hgu⟩ := existsUnique_pCompletedDistinguishedPrismHom
    P.deltaStructure P.generator hd Q hQ f.toRingHom f.map_delta f.map_generator_mem
  refine ⟨g, OrientedPrism.Hom.ext hg, ?_⟩
  intro H hH
  apply hgu H
  exact congrArg OrientedPrism.Hom.toRingHom hH

end Universal

/-- 既に完全なoriented prismでは、p進完備δ完全化上の生成元像のd進完備性も証明できる。
源の実導来条件を古典的条件へ比較し、証明済みの復元同型で運ぶ。 -/
theorem pCompletedPerfectPrism_isAdicComplete_generator
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) :
    IsAdicComplete (Ideal.span {pCompletedDeltaPerfectionMap P.deltaStructure P.generator})
      (PCompletedDeltaPerfection P.deltaStructure) := by
  let := P.isAdicComplete_p_of_perfect hP
  let := P.isAdicComplete_generator
  let e := pCompletedDeltaPerfectionEquiv P.deltaStructure hP
  have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {P.generator}) e).mpr
    (P.isAdicComplete_generator)
  have he : (Ideal.span {P.generator}).map e.toRingHom =
      Ideal.span {pCompletedDeltaPerfectionMap P.deltaStructure P.generator} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  change IsAdicComplete ((Ideal.span {P.generator}).map e.toRingHom)
    (PCompletedDeltaPerfection P.deltaStructure) at h
  rw [he] at h
  exact h

/-- 既に完全なoriented prismのp進完備δ完全化上のprism。
生成元像の完備性を追加仮定せず、上の復元定理で内部に供給する。 -/
def pCompletedPerfectPrism (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) :
    OrientedPrism p (PCompletedDeltaPerfection P.deltaStructure) := by
  let := pCompletedPerfectPrism_isAdicComplete_generator P hP
  exact pCompletedDistinguishedPrism P.deltaStructure P.generator (P.isDistinguished_of_perfect hP)

/-- 復元対象のprismも完全。 -/
theorem pCompletedPerfectPrism_isPerfect (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) : (pCompletedPerfectPrism P hP).deltaStructure.IsPerfect :=
  pCompletedDeltaPerfection_isPerfect P.deltaStructure

/-- 既に完全なprismからの具体的な標準prism射。 -/
def pCompletedPerfectPrismMap (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) :
    OrientedPrism.Hom P (pCompletedPerfectPrism P hP) := by
  let := pCompletedPerfectPrism_isAdicComplete_generator P hP
  exact pCompletedPrismMap P (P.isDistinguished_of_perfect hP)

/-- 既に完全なprismの標準射は、台環で全単射。 -/
theorem pCompletedPerfectPrismMap_bijective (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) :
    Function.Bijective (pCompletedPerfectPrismMap P hP).toRingHom := by
  let := P.isAdicComplete_p_of_perfect hP
  exact pCompletedDeltaPerfectionMap_bijective P.deltaStructure hP

/-- 完全prismの標準射は標準商上でも全単射。 -/
theorem pCompletedPerfectPrismMap_quotientMap_bijective (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) :
    Function.Bijective (pCompletedPerfectPrismMap P hP).quotientMap :=
  (pCompletedPerfectPrismMap P hP).quotientMap_bijective hP
    (pCompletedPerfectPrism_isPerfect P hP) (pCompletedPerfectPrismMap_bijective P hP)

/-- 既に完全なprismへ戻る具体的な逆prism射。既存の同型判定から構成する。 -/
def pCompletedPerfectPrismInverse (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) :
    OrientedPrism.Hom (pCompletedPerfectPrism P hP) P :=
  (pCompletedPerfectPrismMap P hP).inverseOfQuotient hP (pCompletedPerfectPrism_isPerfect P hP)
    (pCompletedPerfectPrismMap_quotientMap_bijective P hP)

/-- 逆prism射と標準prism射の合成は、元prismの恒等射。 -/
@[simp] theorem pCompletedPerfectPrismInverse_comp_map (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) :
    (pCompletedPerfectPrismInverse P hP).comp (pCompletedPerfectPrismMap P hP) =
      OrientedPrism.Hom.id P :=
  (pCompletedPerfectPrismMap P hP).inverseOfQuotient_comp hP
    (pCompletedPerfectPrism_isPerfect P hP) (pCompletedPerfectPrismMap_quotientMap_bijective P hP)

/-- 標準prism射と逆prism射の逆順の合成も、完全化prismの恒等射。 -/
@[simp] theorem pCompletedPerfectPrismMap_comp_inverse (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) :
    (pCompletedPerfectPrismMap P hP).comp (pCompletedPerfectPrismInverse P hP) =
      OrientedPrism.Hom.id (pCompletedPerfectPrism P hP) :=
  (pCompletedPerfectPrismMap P hP).comp_inverseOfQuotient hP
    (pCompletedPerfectPrism_isPerfect P hP) (pCompletedPerfectPrismMap_quotientMap_bijective P hP)

end SerrePositivity.BhattScholze
