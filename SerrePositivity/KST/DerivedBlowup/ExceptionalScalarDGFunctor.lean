module

public import SerrePositivity.KST.DerivedBlowup.ExceptionalBasisScalarNaturality
public import SerrePositivity.KST.DerivedBlowup.ExceptionalChartDGInclusion
public import SerrePositivity.KST.DerivedBlowup.ChartScalarDGFunctor

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子の局所 dg 模型の係数変更。
方針：自由 Koszul の係数変更に関係式の微分移送を合成する。
規約：行先は写した係数・座標の実際の例外因子表示。
使われ方：有限重なり環の射と例外因子の可逆基底変換を組み合わせる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded DifferentialGraded.ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S] {I : Type} [DecidableEq I]

/-- 概要：例外因子の自由 Koszul 係数変更後の微分の標準同定。
方針：関係式列の係数自然性を自由加群の線形形式へ移す。
規約：KST Lemma 3.6。使われ方：係数変更後の行先の移送。 -/
theorem exceptionalScalarDifferential_eq (φ : R →+* S) (a x : I → R) (i : I) :
    Finsupp.linearCombination S (φ ∘ exceptionalRelationValue a x i) =
      Finsupp.linearCombination S (exceptionalRelationValue (φ ∘ a) (φ ∘ x) i) :=
  congrArg (Finsupp.linearCombination S) (exceptionalRelationValue_scalarMap φ a x i)

/-- 概要：実際の例外因子表示の間の dg 係数変更。
方針：自由 Koszul の係数変更と指定微分等式による dg 移送を合成する。
規約：KST Lemma 3.6。使われ方：有限重なり環間の dg 遷移。 -/
def exceptionalScalarDGFunctor (φ : R →+* S) (a x : I → R) (i : I) :
    DGFunctor R
      (ExteriorKoszulObject (Finsupp.linearCombination R (exceptionalRelationValue a x i)))
      (DGRestriction φ (ExteriorKoszulObject
        (Finsupp.linearCombination S (exceptionalRelationValue (φ ∘ a) (φ ∘ x) i)))) :=
  DGFunctor.comp (freeKoszulScalarDGFunctor φ (exceptionalRelationValue a x i))
    (restrictDGFunctor φ (exteriorDifferentialTransportDGFunctor
      (exceptionalScalarDifferential_eq φ a x i)))

/-- 概要：例外因子の dg 係数変更は総外積の標準係数変更と一致する。
方針：微分移送の恒等生成元写像を消去し、自由 Koszul の包含公式を使う。
規約：KST Lemma 3.6。使われ方：係数自然性・合成律の計算。 -/
theorem exceptionalScalarDGFunctor_inclusion (φ : R →+* S) (a x : I → R) (i : I)
    (v w : ExteriorKoszulObject (Finsupp.linearCombination R (exceptionalRelationValue a x i)))
    (q : ℤ) (z : (exteriorKoszulCochain
      (Finsupp.linearCombination R (exceptionalRelationValue a x i))).X q) :
    exteriorCochainInclusion
        (Finsupp.linearCombination S (exceptionalRelationValue (φ ∘ a) (φ ∘ x) i)) q
        (((exceptionalScalarDGFunctor φ a x i).map v w).f q z) =
      freeExteriorScalarMap φ (exteriorCochainInclusion
        (Finsupp.linearCombination R (exceptionalRelationValue a x i)) q z) := by
  change exteriorCochainInclusion
      (Finsupp.linearCombination S (exceptionalRelationValue (φ ∘ a) (φ ∘ x) i)) q
      ((exteriorKoszulCochainMap LinearMap.id _ _ _).f q
        (((freeKoszulScalarDGFunctor φ (exceptionalRelationValue a x i)).map v w).f q z)) = _
  rw [exteriorCochainInclusion_map, ExteriorAlgebra.map_id]
  exact freeKoszulScalarDGFunctor_inclusion φ (exceptionalRelationValue a x i) v w q z

set_option maxHeartbeats 2000000 in
-- 異なる係数環の豊穣 Hom と微分移送を含む二経路の照合に必要。
/-- 概要：共通の全 a_j 表示への例外因子比較は dg 係数変更と可換。
方針：両経路を総外積へ包含し、自己逆基底変換の係数自然性を使う。
規約：KST Lemma 3.6。使われ方：Ko(A;a)[S] 比較の重なり環に関する自然性。 -/
theorem exceptionalExteriorDGFunctor_scalar_natural (φ : R →+* S) (a x : I → R) (i : I) :
    EnrichedFunctor.comp (Complex R)
        (exceptionalExteriorDGFunctor a x i) (freeKoszulScalarDGFunctor φ a) =
      EnrichedFunctor.comp (Complex R) (exceptionalScalarDGFunctor φ a x i)
        (restrictDGFunctor φ (exceptionalExteriorDGFunctor (φ ∘ a) (φ ∘ x) i)) := by
  refine EnrichedFunctor.ext (Complex R)
    (F := EnrichedFunctor.comp (Complex R)
      (exceptionalExteriorDGFunctor a x i) (freeKoszulScalarDGFunctor φ a))
    (G := EnrichedFunctor.comp (Complex R) (exceptionalScalarDGFunctor φ a x i)
      (restrictDGFunctor φ (exceptionalExteriorDGFunctor (φ ∘ a) (φ ∘ x) i))) (fun _ => rfl) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective (Finsupp.linearCombination S (φ ∘ a)) q
  change exteriorCochainInclusion (Finsupp.linearCombination S (φ ∘ a)) q
      (((freeKoszulScalarDGFunctor φ a).map _ _).f q
        ((exteriorKoszulCochainMap (exceptionalGeneratorMap i x) _ _ _).f q z)) =
    exteriorCochainInclusion (Finsupp.linearCombination S (φ ∘ a)) q
      ((exteriorKoszulCochainMap (exceptionalGeneratorMap i (φ ∘ x)) _ _ _).f q
        (((exceptionalScalarDGFunctor φ a x i).map v w).f q z))
  rw [freeKoszulScalarDGFunctor_inclusion, exteriorCochainInclusion_map,
    exteriorCochainInclusion_map, exceptionalScalarDGFunctor_inclusion]
  exact freeExteriorScalarMap_natural φ (exceptionalGeneratorMap i x)
    (exceptionalGeneratorMap i (φ ∘ x)) (exceptionalGeneratorMap_scalarMap φ i x) _

set_option maxHeartbeats 2000000 in
-- 異なる係数環の豊穣 Hom と微分移送を含む二経路の照合に必要。
/-- 概要：例外因子の指定 dg 遷移は係数変更と可換。
方針：全 Hom を総外積へ包含し、遷移の可逆生成元変換の係数自然性を適用する。
規約：KST Lemma 3.6、行先を実際の写した座標の表示とする。
使われ方：異なる有限重なり環を通る cocycle の計算。 -/
theorem exceptionalTransitionDGFunctor_scalar_natural (φ : R →+* S) (a x y : I → R)
    (i k : I) :
    EnrichedFunctor.comp (Complex R) (exceptionalTransitionDGFunctor a x y i k)
        (exceptionalScalarDGFunctor φ a x i) =
      EnrichedFunctor.comp (Complex R) (exceptionalScalarDGFunctor φ a y k)
        (restrictDGFunctor φ (exceptionalTransitionDGFunctor (φ ∘ a) (φ ∘ x) (φ ∘ y) i k)) := by
  refine EnrichedFunctor.ext (Complex R)
    (F := EnrichedFunctor.comp (Complex R) (exceptionalTransitionDGFunctor a x y i k)
      (exceptionalScalarDGFunctor φ a x i))
    (G := EnrichedFunctor.comp (Complex R) (exceptionalScalarDGFunctor φ a y k)
      (restrictDGFunctor φ (exceptionalTransitionDGFunctor (φ ∘ a) (φ ∘ x) (φ ∘ y) i k)))
    (fun _ => rfl) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective
    (Finsupp.linearCombination S (exceptionalRelationValue (φ ∘ a) (φ ∘ x) i)) q
  change exteriorCochainInclusion
      (Finsupp.linearCombination S (exceptionalRelationValue (φ ∘ a) (φ ∘ x) i)) q
      (((exceptionalScalarDGFunctor φ a x i).map _ _).f q
        ((exteriorKoszulCochainMap (exceptionalTransitionEquiv i k x y).toLinearMap _ _ _).f q z)) =
    exteriorCochainInclusion
      (Finsupp.linearCombination S (exceptionalRelationValue (φ ∘ a) (φ ∘ x) i)) q
      ((exteriorKoszulCochainMap
        (exceptionalTransitionEquiv i k (φ ∘ x) (φ ∘ y)).toLinearMap _ _ _).f q
        (((exceptionalScalarDGFunctor φ a y k).map v w).f q z))
  rw [exceptionalScalarDGFunctor_inclusion, exteriorCochainInclusion_map,
    exteriorCochainInclusion_map, exceptionalScalarDGFunctor_inclusion]
  exact freeExteriorScalarMap_natural φ (exceptionalTransitionEquiv i k x y).toLinearMap
    (exceptionalTransitionEquiv i k (φ ∘ x) (φ ∘ y)).toLinearMap
    (exceptionalTransitionEquiv_scalarMap φ i k x y) _

end SerrePositivity.KST.DerivedBlowup
