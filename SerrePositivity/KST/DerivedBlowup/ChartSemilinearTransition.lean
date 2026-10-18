module

public import SerrePositivity.KST.DerivedBlowup.ChartScalarDGFunctor

/-!
概要：KST §3.1 の異なる係数環のチャート模型の間の実際の dg 遷移。
方針：係数変更、関係式の微分移送、目標チャートの可逆基底変換を合成する。
規約：環射が元の座標を目標座標の規格化へ送る条件を明示する。
使われ方：全有限重なり環の図式を dg チャート模型へ持ち上げる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S] {I : Type} [DecidableEq I]

/-- 概要：環射と pivot 変更を同時に行うチャート dg 遷移。
方針：元チャートの係数変更を、規格化座標の微分移送と目標の基底変換へ接続する。
規約：KST §3.1、i が元 pivot、k が目標 pivot。
使われ方：有限重なりの拡大と pivot 変更をまとめた dg 関手。 -/
def chartSemilinearDGFunctor (φ : R →+* S) (a x : I → R) (b y : I → S)
    (i k : I) (s : Sˣ) (ha : φ ∘ a = b) (hx : φ ∘ x = normalizeCoordinates y s)
    (hk : y k = 1) (hs : ↑s = y i) :
    DGFunctor R (ExteriorKoszulObject (chartKoszulDifferential a x i))
      (DGRestriction φ (ExteriorKoszulObject (chartKoszulDifferential b y k))) :=
  EnrichedFunctor.comp (Complex R) (chartScalarDGFunctor φ a x i)
    (restrictDGFunctor φ (EnrichedFunctor.comp (Complex S)
      (exteriorDifferentialTransportDGFunctor
        (congrArg₂ (fun c z => chartKoszulDifferential c z i) ha hx))
      (chartExteriorDGFunctor b y k i s hk hs)))

/-- 概要：環射と pivot 変更の dg 遷移の Hom は総外積で具体的に計算できる。
方針：係数変更・微分移送・基底変換の包含公式を順に適用する。
規約：KST §3.1。使われ方：有限重なり dg 遷移の恒等・合成整合性。 -/
theorem chartSemilinearDGFunctor_inclusion (φ : R →+* S) (a x : I → R) (b y : I → S)
    (i k : I) (s : Sˣ) (ha : φ ∘ a = b) (hx : φ ∘ x = normalizeCoordinates y s)
    (hk : y k = 1) (hs : ↑s = y i)
    (v w : ExteriorKoszulObject (chartKoszulDifferential a x i)) (q : ℤ)
    (z : (exteriorKoszulCochain (chartKoszulDifferential a x i)).X q) :
    exteriorCochainInclusion (chartKoszulDifferential b y k) q
        (((chartSemilinearDGFunctor φ a x b y i k s ha hx hk hs).map v w).f q z) =
      ExteriorAlgebra.map (koszulGeneratorMap k i y s)
        (freeExteriorScalarMap φ
          (exteriorCochainInclusion (chartKoszulDifferential a x i) q z)) := by
  change exteriorCochainInclusion (chartKoszulDifferential b y k) q
    ((exteriorKoszulCochainMap (koszulGeneratorMap k i y s)
      (chartKoszulDifferential b (normalizeCoordinates y s) i)
      (chartKoszulDifferential b y k) _).f q
      ((exteriorKoszulCochainMap LinearMap.id
        (chartKoszulDifferential (φ ∘ a) (φ ∘ x) i)
        (chartKoszulDifferential b (normalizeCoordinates y s) i) _).f q
        (((chartScalarDGFunctor φ a x i).map v w).f q z))) = _
  rw [exteriorCochainInclusion_map, exteriorCochainInclusion_map,
    ExteriorAlgebra.map_id, chartScalarDGFunctor_inclusion]
  rfl

end SerrePositivity.KST.DerivedBlowup
