module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.Module.FinitePresentation

/-!
概要：KST §5、Stacks 0815 の有限表示平坦加群の基本開上の自由化。
方針：局所環上の自由性を有限表示加群の局所化同型の降下で基本開へ広げる。
規約：階数の大域的な一定性は仮定しない。
使われ方：境界外で平坦な有限加群の局所的な自由基底の選択。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
  [Module.FinitePresentation R M] [Module.Flat R M]

/--
概要：有限表示平坦加群は各素点を含むある基本開集合上で自由。
方針：素点の局所化での有限自由基底を有限表示性で基本開へ降ろす。
規約：KST §5、Stacks 0815、基本開の元と局所化加群の自由性を実際に返す。
使われ方：境界外が平坦という仮定から自由な基本開被覆を選ぶ。
-/
theorem finite_flat_exists_away_free (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, Module.Free (Localization.Away r) (LocalizedModule.Away r M) := by
  classical
  let Rp := Localization.AtPrime p
  let Mp := LocalizedModule.AtPrime p M
  let : Module.Free Rp Mp := Module.free_of_flat_of_isLocalRing
  let n := Module.finrank Rp Mp
  let ep : Mp ≃ₗ[Rp] (Fin n → Rp) :=
    (Module.finBasis Rp Mp).repr.trans (Finsupp.linearEquivFunOnFinite Rp Rp (Fin n))
  let μ : M →ₗ[R] Mp := LocalizedModule.mkLinearMap p.primeCompl M
  let ν : (Fin n → R) →ₗ[R] (Fin n → Rp) :=
    LinearMap.pi (fun i => (Algebra.linearMap R Rp).comp (LinearMap.proj i))
  have : IsLocalizedModule p.primeCompl ν := inferInstance
  obtain ⟨r, hr, e, _⟩ :=
    Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule p.primeCompl μ ν
      (ep.restrictScalars R)
  have : Module.Free (Localization.Away r) (LocalizedModule.Away r (Fin n → R)) :=
    Module.free_of_isLocalizedModule (Submonoid.powers r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) (Fin n → R))
  exact ⟨r, hr, Module.Free.of_equiv e.symm⟩

/--
概要：加群が局所化後に自由となる元の集合。
方針：基本開集合の係数となる環の元で添字付けする。
規約：KST §5、Stacks 0815、定義自体に有限表示性や平坦性は不要。
使われ方：自由な基本開被覆の単位イデアル生成の表現。
-/
def freeLocalizationElements : Set R :=
  {r | Module.Free (Localization.Away r) (LocalizedModule.Away r M)}

/--
概要：有限表示平坦加群が自由となる基本開の係数は単位イデアルを生成する。
方針：真のイデアルを含む極大イデアルに対して自由な近傍の存在を適用する。
規約：KST §5、Stacks 0815、階数は被覆の各部分で異なってよい。
使われ方：境界外の自由な基本開の有限被覆を選ぶ準備。
-/
theorem span_freeLocalizationElements_eq_top :
    Ideal.span (freeLocalizationElements (R := R) M) = ⊤ := by
  classical
  by_contra h
  obtain ⟨p, hp, hIp⟩ := (Ideal.span (freeLocalizationElements (R := R) M)).exists_le_maximal h
  let : p.IsMaximal := hp
  obtain ⟨r, hr, hfree⟩ := finite_flat_exists_away_free M p
  exact hr (hIp (Ideal.subset_span hfree))

/--
概要：有限表示平坦加群を自由にする基本開は有限部分族で全体を覆う。
方針：単位イデアルの生成に必要な有限個の元を取り出す。
規約：KST §5、Stacks 0815、自由な局所化の係数を有限集合として返す。
使われ方：境界外の自由化被覆の有限性。
-/
theorem exists_finset_freeLocalizations :
    ∃ s : Finset R, (∀ r ∈ s, r ∈ freeLocalizationElements (R := R) M) ∧
      Ideal.span (s : Set R) = ⊤ := by
  classical
  exact (Ideal.span_eq_top_iff_finite _).mp (span_freeLocalizationElements_eq_top M)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
