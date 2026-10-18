module

public import SerrePositivity.KST.DerivedGeometry.AcyclicMapAttachment
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
概要：非有界複体の K-injective 性を単射準同型に対する右持ち上げから得る。
方針：acyclic 始域の contractible な埋め込みを持ち上げ、縮約を合成する。
規約：分解の存在をこの判定の仮定として与えない。
使われ方：Stacks 19.12.3・19.12.6、TT §3・§8、Toën §3.2 の非有界 K-injective 分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits ZeroObject
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]

/--
概要：contractible な埋め込みに対する持ち上げは指定した射の零ホモトピーを与える。
方針：持ち上げ射に埋め込み先の縮約を合成する。
規約：始域の非輪状性はこのホモトピー自体に不要。
使われ方：Stacks 19.12.3、TT §3 の K-injective 判定。
-/
def homotopyZero_of_envelope_lifting (A I : CochainComplex C ℤ) (f : A ⟶ I)
    [HasLiftingProperty (termInjectiveEnvelopeι A) (0 : I ⟶ 0)] : Homotopy f 0 := by
  let sq : CommSq f (termInjectiveEnvelopeι A) (0 : I ⟶ 0) (0 : termInjectiveEnvelope A ⟶ 0) :=
    ⟨by simp⟩
  have h : Homotopy (termInjectiveEnvelopeι A) 0 := by
    simpa using (adjacentBiproductContraction (fun n => Injective.under (A.X n))).compLeft
      (termInjectiveEnvelopeι A)
  have ht : Homotopy (termInjectiveEnvelopeι A ≫ sq.lift) 0 := by
    simpa only [zero_comp] using h.compRight sq.lift
  exact (Homotopy.ofEq sq.fac_left.symm).trans ht

/--
概要：全ての acyclic 始域の contractible な埋め込みを持ち上げる複体は K-injective。
方針：構成済みの零ホモトピーを任意の acyclic 始域からの射に適用する。
規約：各項の injectivity による代用をしない。
使われ方：Stacks 19.12.3・19.12.6、TT §3 の非有界分解の判定。
-/
lemma isKInjective_of_envelope_lifting (I : CochainComplex C ℤ)
    (h : ∀ (A : CochainComplex C ℤ), A.Acyclic →
      HasLiftingProperty (termInjectiveEnvelopeι A) (0 : I ⟶ 0)) : I.IsKInjective where
  nonempty_homotopy_zero {A} f hA := by
    have := h A hA
    exact ⟨homotopyZero_of_envelope_lifting A I f⟩

/--
概要：全ての単射準同型に対する右持ち上げを持つ複体は K-injective。
方針：acyclic 始域の contractible な単射は準同型であることを使う。
規約：右持ち上げ性から K-injective 性を証明する判定であり、分解の存在とは区別する。
使われ方：Stacks 19.12.6、TT §3・§8、Toën §3.2 の非有界 injective 模型。
-/
lemma isKInjective_of_rlp_mono_quasiIso (I : CochainComplex C ℤ)
    (h : ((MorphismProperty.monomorphisms (CochainComplex C ℤ)) ⊓
      HomologicalComplex.quasiIso C (.up ℤ)).rlp (0 : I ⟶ 0)) : I.IsKInjective := by
  apply isKInjective_of_envelope_lifting I
  intro A hA
  apply h (termInjectiveEnvelopeι A)
  exact ⟨inferInstance, quasiIso_of_acyclic A _ _ hA (adjacentBiproductComplex_acyclic _)⟩

end SerrePositivity.KST.DerivedGeometry
