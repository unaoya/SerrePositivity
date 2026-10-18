module

public import SerrePositivity.KST.DerivedBlowup.FreeKoszulScalarDGFunctor
public import SerrePositivity.KST.DerivedBlowup.ChartDGCocycle

/-!
概要：KST §3.1 の規格化座標表示のチャート模型の dg 係数変更。
方針：自由 Koszul の係数変更後、環射の乗法・減法保存による微分移送を適用する。
規約：行先を写した係数と座標で定義した実際のチャート外積模型とする。
使われ方：有限重なりの係数環変更と可逆基底変換を組み合わせる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S] {I : Type} [DecidableEq I]

omit [DecidableEq I] in
/-- 概要：係数変更したチャート関係式の微分は写した係数・座標の微分に等しい。
方針：各関係式で環射の乗法・減法保存を使う。
規約：KST §3.1。使われ方：底変更後のチャート微分の標準同定。 -/
theorem chartScalarDifferential_eq (φ : R →+* S) (a x : I → R) (i : I) :
    Finsupp.linearCombination S
      (φ ∘ (fun j : ChartIndex i => a i * x j.val - a j.val)) =
      chartKoszulDifferential (φ ∘ a) (φ ∘ x) i := by
  congr 1
  funext j
  exact (map_sub φ _ _).trans (congrArg (fun z => z - φ (a j.val)) (map_mul φ _ _))

/-- 概要：環射に沿うチャート外積模型の dg 関手。
方針：自由 Koszul の係数変更にチャート微分の等式による移送を合成する。
規約：KST §3.1。使われ方：係数環が変わるチャート dg 遷移。 -/
def chartScalarDGFunctor (φ : R →+* S) (a x : I → R) (i : I) :
    DGFunctor R (ExteriorKoszulObject (chartKoszulDifferential a x i))
      (DGRestriction φ
        (ExteriorKoszulObject (chartKoszulDifferential (φ ∘ a) (φ ∘ x) i))) :=
  EnrichedFunctor.comp (Complex R)
    (freeKoszulScalarDGFunctor φ (fun j : ChartIndex i => a i * x j.val - a j.val))
    (restrictDGFunctor φ (exteriorDifferentialTransportDGFunctor
      (chartScalarDifferential_eq φ a x i)))

/-- 概要：チャート dg 係数変更の Hom は総外積の標準係数変更で計算できる。
方針：微分移送の恒等生成元写像と自由 Koszul の包含公式を使う。
規約：KST §3.1。使われ方：基底変換との dg 自然性と合成律。 -/
theorem chartScalarDGFunctor_inclusion (φ : R →+* S) (a x : I → R) (i : I)
    (v w : ExteriorKoszulObject (chartKoszulDifferential a x i)) (q : ℤ)
    (z : (exteriorKoszulCochain (chartKoszulDifferential a x i)).X q) :
    exteriorCochainInclusion (chartKoszulDifferential (φ ∘ a) (φ ∘ x) i) q
        (((chartScalarDGFunctor φ a x i).map v w).f q z) =
      freeExteriorScalarMap φ (exteriorCochainInclusion (chartKoszulDifferential a x i) q z) := by
  change exteriorCochainInclusion (chartKoszulDifferential (φ ∘ a) (φ ∘ x) i) q
    ((exteriorKoszulCochainMap LinearMap.id _ _ _).f q
      (((freeKoszulScalarDGFunctor φ
        (fun j : ChartIndex i => a i * x j.val - a j.val)).map v w).f q z)) = _
  rw [exteriorCochainInclusion_map, ExteriorAlgebra.map_id]
  exact freeKoszulScalarDGFunctor_inclusion φ
    (fun j : ChartIndex i => a i * x j.val - a j.val) v w q z

end SerrePositivity.KST.DerivedBlowup
