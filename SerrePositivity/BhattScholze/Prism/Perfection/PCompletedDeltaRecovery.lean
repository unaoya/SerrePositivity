module

public import SerrePositivity.BhattScholze.Prism.Perfection.PCompletedDeltaFunctor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.AdicComparison

/-! # 完全p進完備δ環のp進完備δ完全化からの復元

著者公開版Lemma 3.9のp進完備化段階の冪等性。
既に完全かつ古典的p進完備なδ環の標準射は同型で、逆射もδ射。
一般Witt復元、prismの完全化、perfectoid化の存在とは別の具体的な定理。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

section Recovery
variable (D : DeltaStructure p A) (hD : D.IsPerfect)
variable [IsAdicComplete (Ideal.span {(p : A)}) A]

/-- 完全p進完備δ環への、恒等基底射を延長した具体的な復元射。 -/
def pCompletedDeltaRetract : PCompletedDeltaPerfection D →+* A :=
  pCompletedDeltaLift D D hD (RingHom.id A) D.isDeltaHom_id

/-- 復元射はδ射。 -/
theorem pCompletedDeltaRetract_isDeltaHom :
    (pCompletedDeltaPerfectionStructure D).IsDeltaHom D (pCompletedDeltaRetract D hD) :=
  pCompletedDeltaLift_isDeltaHom D D hD _ _

/-- 復元射と元の標準射の合成は元環の恒等射。 -/
@[simp] theorem pCompletedDeltaRetract_comp_map :
    (pCompletedDeltaRetract D hD).comp (pCompletedDeltaPerfectionMap D) = RingHom.id A :=
  pCompletedDeltaLift_comp_map D D hD _ _

/-- 標準射と復元射の逆順の合成も、完備δ完全化の恒等射。 -/
@[simp] theorem pCompletedDeltaMap_comp_retract :
    (pCompletedDeltaPerfectionMap D).comp (pCompletedDeltaRetract D hD) =
      RingHom.id (PCompletedDeltaPerfection D) := by
  let := pCompletedDeltaPerfection_isAdicComplete D
  apply pCompletedDeltaHom_ext D _ (pCompletedDeltaPerfection_isPerfect D) _ _
    ((pCompletedDeltaPerfectionMap_isDeltaHom D).comp (pCompletedDeltaRetract_isDeltaHom D hD))
    (pCompletedDeltaPerfectionStructure D).isDeltaHom_id
  rw [RingHom.comp_assoc, pCompletedDeltaRetract_comp_map, RingHom.comp_id, RingHom.id_comp]

include hD in
/-- 完全p進完備δ環の標準p進完備δ完全化射は全単射。 -/
theorem pCompletedDeltaPerfectionMap_bijective :
    Function.Bijective (pCompletedDeltaPerfectionMap D) := by
  have hl : Function.LeftInverse (pCompletedDeltaRetract D hD) (pCompletedDeltaPerfectionMap D) :=
    fun x ↦ RingHom.congr_fun (pCompletedDeltaRetract_comp_map D hD) x
  have hr : Function.RightInverse (pCompletedDeltaRetract D hD) (pCompletedDeltaPerfectionMap D) :=
    fun x ↦ RingHom.congr_fun (pCompletedDeltaMap_comp_retract D hD) x
  exact ⟨hl.injective, hr.surjective⟩

/-- 完全p進完備δ環と、その具体的なp進完備δ完全化の環同型。 -/
def pCompletedDeltaPerfectionEquiv : A ≃+* PCompletedDeltaPerfection D :=
  RingEquiv.ofBijective (pCompletedDeltaPerfectionMap D)
    (pCompletedDeltaPerfectionMap_bijective D hD)

/-- 復元同型の順射は標準射。 -/
@[simp] theorem pCompletedDeltaPerfectionEquiv_toRingHom :
    (pCompletedDeltaPerfectionEquiv D hD).toRingHom = pCompletedDeltaPerfectionMap D := rfl

/-- 復元同型の逆射は恒等基底射の一意延長として選んだ復元射。 -/
@[simp] theorem pCompletedDeltaPerfectionEquiv_symm_toRingHom :
    (pCompletedDeltaPerfectionEquiv D hD).symm.toRingHom = pCompletedDeltaRetract D hD := by
  apply RingHom.ext
  intro x
  apply (pCompletedDeltaPerfectionMap_bijective D hD).1
  change (pCompletedDeltaPerfectionEquiv D hD)
    ((pCompletedDeltaPerfectionEquiv D hD).symm x) =
      pCompletedDeltaPerfectionMap D (pCompletedDeltaRetract D hD x)
  rw [RingEquiv.apply_symm_apply]
  exact (RingHom.congr_fun (pCompletedDeltaMap_comp_retract D hD) x).symm

/-- 復元同型は具体的な主イデアルによる商にも標準写像と両立する同型を誘導する。 -/
def pCompletedDeltaPerfectionQuotientEquiv (d : A) :
    A ⧸ Ideal.span {d} ≃+*
      PCompletedDeltaPerfection D ⧸ Ideal.span {pCompletedDeltaPerfectionMap D d} :=
  Ideal.quotientEquiv _ _ (pCompletedDeltaPerfectionEquiv D hD)
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)

/-- 誘導商同型は、代表元に標準p進完備δ完全化射を適用する。 -/
@[simp] theorem pCompletedDeltaPerfectionQuotientEquiv_mk (d x : A) :
    pCompletedDeltaPerfectionQuotientEquiv D hD d (Ideal.Quotient.mk (Ideal.span {d}) x) =
      Ideal.Quotient.mk (Ideal.span {pCompletedDeltaPerfectionMap D d})
        (pCompletedDeltaPerfectionMap D x) := rfl

end Recovery

/-- 任意のδ環のp進完備δ完全化をもう一度同じ操作で完全化しても同型。
任意の源のp正則性・古典的完備性は要求しない。 -/
def pCompletedDeltaPerfectionIdempotentEquiv (D : DeltaStructure p A) :
    PCompletedDeltaPerfection D ≃+*
      PCompletedDeltaPerfection (pCompletedDeltaPerfectionStructure D) := by
  let := pCompletedDeltaPerfection_isAdicComplete D
  exact pCompletedDeltaPerfectionEquiv _ (pCompletedDeltaPerfection_isPerfect D)

/-- 冪等同型の順射は二段目の標準射。 -/
@[simp] theorem pCompletedDeltaPerfectionIdempotentEquiv_toRingHom (D : DeltaStructure p A) :
    (pCompletedDeltaPerfectionIdempotentEquiv D).toRingHom =
      pCompletedDeltaPerfectionMap (pCompletedDeltaPerfectionStructure D) := rfl

/-- 具体的なp進完備δ完全化は実導来p完備でもある。
共通の古典的完備→導来完備比較を適用し、導来完備化対象との同定は結論しない。 -/
theorem pCompletedDeltaPerfection_isModuleComplete (D : DeltaStructure p A) :
    DerivedCompletion.IsModuleComplete (PCompletedDeltaPerfection D)
      (p : PCompletedDeltaPerfection D)
      (ModuleCat.of (PCompletedDeltaPerfection D) (PCompletedDeltaPerfection D)) := by
  let := pCompletedDeltaPerfection_isAdicComplete D
  exact DerivedCompletion.isModuleComplete_of_isAdicComplete (PCompletedDeltaPerfection D)
    (p : PCompletedDeltaPerfection D) _

end SerrePositivity.BhattScholze
