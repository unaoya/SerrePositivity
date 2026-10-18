module

public import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeDGFunctor
public import SerrePositivity.KST.DerivedBlowup.ExteriorDGFunctor
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
概要：KST Def3.1 の自由生成元で表示した Koszul dg 圏の底変更。
方針：S⊗(I→₀R)≃(I→₀S) と線形結合微分の比較を使う。
規約：標準チャートで使う小さい添字型を扱う。有限性は要求しない。
使われ方：チャート環の環射による Koszul dg 圏のスカラー拡大比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open scoped TensorProduct

variable {R S : Type u} [CommRing R] [CommRing S] {I : Type} [DecidableEq I]

/-- 概要：自由生成加群のスカラー拡大の標準同型。
方針：既存 finsuppScalarRight を用いる。
規約：KST Def3.1。使われ方：チャート関係式の生成元の係数変更。 -/
def freeKoszulBaseChangeGeneratorEquiv (φ : R →+* S) (I : Type) [DecidableEq I] :
    letI := φ.toAlgebra
    S ⊗[R] (I →₀ R) ≃ₗ[S] (I →₀ S) := by
  letI := φ.toAlgebra
  exact TensorProduct.finsuppScalarRight R S S I

/-- 概要：自由生成加群の標準底変更同型は Koszul の線形結合微分を保つ。
方針：同型の逆で前合成し、単一生成元における微分の値を比較する。
規約：KST Def3.1。使われ方：自由 Koszul 底変更 dg 関手の chain 条件。 -/
theorem freeKoszulBaseChangeGeneratorEquiv_differential (φ : R →+* S) (a : I → R) :
    letI := φ.toAlgebra
    (Finsupp.linearCombination S (φ ∘ a)).comp
        (freeKoszulBaseChangeGeneratorEquiv φ I).toLinearMap =
      exteriorBaseChangeDifferential (S := S) (Finsupp.linearCombination R a) := by
  let := φ.toAlgebra
  apply (LinearMap.cancel_right (freeKoszulBaseChangeGeneratorEquiv φ I).symm.surjective).mp
  apply Finsupp.lhom_ext
  intro i s
  simp [LinearMap.comp_apply, freeKoszulBaseChangeGeneratorEquiv,
    TensorProduct.finsuppScalarRight_symm_apply_single, TensorProduct.finsuppScalarRight_apply_tmul,
    exteriorBaseChangeDifferential_tmul]
  rfl

/-- 概要：自由生成元表示の Koszul dg 圏の係数変更から係数像の Koszul dg 圏への dg 関手。
方針：一般の Koszul 底変更関手と自由生成加群同型による dg 関手を合成する。
規約：KST Def3.1。使われ方：チャートの底変更後の dg 代数。 -/
def freeKoszulBaseChangeDGFunctor (φ : R →+* S) (a : I → R) :
    letI := φ.toAlgebra
    EnrichedFunctor (DifferentialGraded.Complex S)
      (DifferentialGraded.ScalarExtension.DGBaseChange φ
        (ExteriorKoszulObject (Finsupp.linearCombination R a)))
      (ExteriorKoszulObject (Finsupp.linearCombination S (φ ∘ a))) := by
  letI := φ.toAlgebra
  exact EnrichedFunctor.comp (DifferentialGraded.Complex S)
    (exteriorKoszulBaseChangeDGFunctor φ (Finsupp.linearCombination R a))
    (exteriorKoszulDGFunctor (freeKoszulBaseChangeGeneratorEquiv φ I).toLinearMap
      (exteriorBaseChangeDifferential (S := S) (Finsupp.linearCombination R a))
      (Finsupp.linearCombination S (φ ∘ a))
      (freeKoszulBaseChangeGeneratorEquiv_differential φ a))

/-- 概要：自由 Koszul 底変更 dg 関手の Hom 写像は複体同型。
方針：一般の底変更同型と自由生成加群の外積同型の合成として比較する。
規約：KST Def3.1。使われ方：チャート底変更の局所 dg 同値性。 -/
theorem freeKoszulBaseChangeDGFunctor_map_isIso (φ : R →+* S) (a : I → R) :
    letI := φ.toAlgebra
    ∀ x y, IsIso ((freeKoszulBaseChangeDGFunctor φ a).map x y) := by
  let := φ.toAlgebra
  intro x y
  change IsIso ((exteriorCochainBaseChangeIso φ (Finsupp.linearCombination R a)).inv ≫
    (exteriorKoszulCochainIso (freeKoszulBaseChangeGeneratorEquiv φ I)
      (exteriorBaseChangeDifferential (S := S) (Finsupp.linearCombination R a))
      (Finsupp.linearCombination S (φ ∘ a))
      (freeKoszulBaseChangeGeneratorEquiv_differential φ a)).hom)
  infer_instance

/-- 概要：自由 Koszul dg 圏の底変更比較は準同値。
方針：Hom の複体同型と一対象の H⁰ 上の全射性を使う。
規約：KST Def3.1。使われ方：チャート環射のスカラー拡大の比較。 -/
theorem freeKoszulBaseChangeDGFunctor_quasiEquivalence (φ : R →+* S) (a : I → R) :
    letI := φ.toAlgebra
    DifferentialGraded.QuasiEquivalence (freeKoszulBaseChangeDGFunctor φ a) := by
  let := φ.toAlgebra
  constructor
  · intro x y
    have := freeKoszulBaseChangeDGFunctor_map_isIso φ a x y
    infer_instance
  · apply Functor.essSurj_of_surj
    rintro ⟨y⟩
    change ExteriorKoszulObject (Finsupp.linearCombination S (φ ∘ a)) at y
    cases y
    exact ⟨⟨ExteriorKoszulObject.point⟩, rfl⟩

end SerrePositivity.KST.DerivedBlowup
