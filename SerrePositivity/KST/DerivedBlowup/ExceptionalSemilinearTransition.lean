module

public import SerrePositivity.KST.DerivedBlowup.ExceptionalScalarDGFunctor

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子の係数環と pivot を同時に変える。
方針：実際の dg 係数変更に、行先環上の可逆生成元変換を合成する。
規約：基底係数の一致を明示し、行先は元の係数環への制限とする。
使われ方：実際の有限重なり環に沿う例外因子の dg 遷移。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded DifferentialGraded.ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S] {I : Type} [DecidableEq I]

/-- 概要：係数変更と pivot 変更を合わせた例外因子の指定 dg 射。
方針：係数関数の等式を移送し、係数変更後に共通 Koszul 表示を介して pivot を変える。
規約：KST Lemma 3.6、i から k へ向く。使われ方：有限重なりの例外因子遷移。 -/
def exceptionalSemilinearDGFunctor (φ : R →+* S) (a x : I → R) (b y : I → S)
    (i k : I) (ha : φ ∘ a = b) :
    DGFunctor R
      (ExteriorKoszulObject (Finsupp.linearCombination R (exceptionalRelationValue a x i)))
      (DGRestriction φ
        (ExteriorKoszulObject (Finsupp.linearCombination S (exceptionalRelationValue b y k)))) := by
  subst b
  exact EnrichedFunctor.comp (Complex R) (exceptionalScalarDGFunctor φ a x i)
    (restrictDGFunctor φ (exceptionalTransitionDGFunctor (φ ∘ a) y (φ ∘ x) k i))

/-- 概要：例外因子の半線形 dg 遷移は係数変更と可逆基底変換で計算できる。
方針：総外積への包含により、二つの既存 dg 関手の成分公式を合成する。
規約：KST Lemma 3.6。使われ方：実際の重なりでの比較と cocycle。 -/
theorem exceptionalSemilinearDGFunctor_inclusion (φ : R →+* S) (a x : I → R) (b y : I → S)
    (i k : I) (ha : φ ∘ a = b)
    (v w : ExteriorKoszulObject (Finsupp.linearCombination R (exceptionalRelationValue a x i)))
    (q : ℤ) (z : (exteriorKoszulCochain
      (Finsupp.linearCombination R (exceptionalRelationValue a x i))).X q) :
    exteriorCochainInclusion (Finsupp.linearCombination S (exceptionalRelationValue b y k)) q
        (((exceptionalSemilinearDGFunctor φ a x b y i k ha).map v w).f q z) =
      ExteriorAlgebra.map (exceptionalTransitionEquiv k i y (φ ∘ x)).toLinearMap
        (freeExteriorScalarMap φ (exteriorCochainInclusion
          (Finsupp.linearCombination R (exceptionalRelationValue a x i)) q z)) := by
  subst b
  change exteriorCochainInclusion
      (Finsupp.linearCombination S (exceptionalRelationValue (φ ∘ a) y k)) q
      ((exteriorKoszulCochainMap (exceptionalTransitionEquiv k i y (φ ∘ x)).toLinearMap _ _ _).f q
        (((exceptionalScalarDGFunctor φ a x i).map v w).f q z)) = _
  rw [exteriorCochainInclusion_map, exceptionalScalarDGFunctor_inclusion]

/-- 概要：半線形例外因子遷移は共通の全 a_j 表示への比較と可換。
方針：行先の基底変換を消去し、始点の基底変換の係数自然性を使う。
規約：KST Lemma 3.6。使われ方：有限重なり環間の共通 Koszul 表示の整合性。 -/
theorem exceptionalSemilinearDGFunctor_comparison (φ : R →+* S) (a x : I → R) (b y : I → S)
    (i k : I) (ha : φ ∘ a = b)
    (v w : ExteriorKoszulObject (Finsupp.linearCombination R (exceptionalRelationValue a x i)))
    (q : ℤ) (z : (exteriorKoszulCochain
      (Finsupp.linearCombination R (exceptionalRelationValue a x i))).X q) :
    ExteriorAlgebra.map (exceptionalGeneratorMap k y)
        (exteriorCochainInclusion (Finsupp.linearCombination S (exceptionalRelationValue b y k)) q
          (((exceptionalSemilinearDGFunctor φ a x b y i k ha).map v w).f q z)) =
      freeExteriorScalarMap φ (ExteriorAlgebra.map (exceptionalGeneratorMap i x)
        (exteriorCochainInclusion
          (Finsupp.linearCombination R (exceptionalRelationValue a x i)) q z)) := by
  rw [exceptionalSemilinearDGFunctor_inclusion]
  have h : (exceptionalGeneratorMap k y).comp
      (exceptionalTransitionEquiv k i y (φ ∘ x)).toLinearMap =
        exceptionalGeneratorMap i (φ ∘ x) := by
    apply LinearMap.ext
    exact exceptionalTransitionEquiv_comparison k i y (φ ∘ x)
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h]
  exact (freeExteriorScalarMap_natural φ (exceptionalGeneratorMap i x)
    (exceptionalGeneratorMap i (φ ∘ x)) (exceptionalGeneratorMap_scalarMap φ i x) _).symm

end SerrePositivity.KST.DerivedBlowup
