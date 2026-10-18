module

public import SerrePositivity.KST.DerivedBlowup.ChartDGFunctors
public import SerrePositivity.KST.DerivedBlowup.ChartCochainCocycle

/-!
概要：KST §3.1 の三重重なりの Koszul 遷移を dg 関手の cocycle として示す。
方針：規格化座標の等式による微分移送関手を明示し、Hom 上の cochain cocycle を使う。
規約：同一係数環上の遷移。係数環間の底変更比較は別に組み合わせる。
使われ方：全有限重なり図式の局所 dg 環の整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：微分の等式に沿う一対象 Koszul dg 圏の移送関手。
方針：恒等生成元写像を微分等式とともに dg 関手へ持ち上げる。
規約：KST Def3.1。使われ方：二重規格化と一重規格化の比較。 -/
def exteriorDifferentialTransportDGFunctor {d d' : M →ₗ[R] R} (h : d = d') :
    EnrichedFunctor (DifferentialGraded.Complex R)
      (ExteriorKoszulObject d) (ExteriorKoszulObject d') :=
  exteriorKoszulDGFunctor LinearMap.id d d' (by rw [LinearMap.comp_id]; exact h.symm)

/-- 概要：微分移送関手の Hom は複体の等式移送。
方針：微分等式を消去して恒等射の関手性を使う。
規約：KST Def3.1。使われ方：dg 関手の cocycle を cochain cocycle へ帰着する。 -/
theorem exteriorDifferentialTransportDGFunctor_map {d d' : M →ₗ[R] R} (h : d = d') :
    (exteriorDifferentialTransportDGFunctor h).map .point .point =
      eqToHom (congrArg exteriorKoszulCochain h) := by
  subst d'
  change exteriorKoszulCochainMap LinearMap.id d d _ = _
  rw [exteriorKoszulCochainMap_id]
  rfl

variable {B : Type (max u v)} [CommRing B] {I : Type v} [DecidableEq I]

/-- 概要：三重重なりの二つの dg 遷移の合成は直接遷移に等しい。
方針：一対象型の対象写像を比較し、Hom では既存の cochain cocycle を使う。
規約：KST §3.1、二重規格化の始域同定を微分移送関手で明示する。
使われ方：チャートの dg 図式の合成整合性。 -/
theorem chartExteriorDGFunctor_cocycle (a x : I → B) (i k l : I) (s t : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) (ht : ↑t = normalizeCoordinates x s l) :
    EnrichedFunctor.comp (DifferentialGraded.Complex B)
      (chartExteriorDGFunctor a (normalizeCoordinates x s) k l t
        (normalizeCoordinates_pivot x k s hs) ht)
      (chartExteriorDGFunctor a x i k s hi hs) =
    EnrichedFunctor.comp (DifferentialGraded.Complex B)
      (exteriorDifferentialTransportDGFunctor
        (congrArg (fun y => chartKoszulDifferential a y l) (normalizeCoordinates_cocycle x s t)))
      (chartExteriorDGFunctor a x i l (s * t) hi (transitionUnit_cocycle x l s t ht)) := by
  refine EnrichedFunctor.ext (DifferentialGraded.Complex B)
    (F := EnrichedFunctor.comp (DifferentialGraded.Complex B)
      (chartExteriorDGFunctor a (normalizeCoordinates x s) k l t
        (normalizeCoordinates_pivot x k s hs) ht)
      (chartExteriorDGFunctor a x i k s hi hs))
    (G := EnrichedFunctor.comp (DifferentialGraded.Complex B)
      (exteriorDifferentialTransportDGFunctor
        (congrArg (fun y => chartKoszulDifferential a y l) (normalizeCoordinates_cocycle x s t)))
      (chartExteriorDGFunctor a x i l (s * t) hi (transitionUnit_cocycle x l s t ht)))
    (fun _ => rfl) ?_
  intro z w
  change chartExteriorCochainMap a (normalizeCoordinates x s) k l t
      (normalizeCoordinates_pivot x k s hs) ht ≫ chartExteriorCochainMap a x i k s hi hs =
    (exteriorDifferentialTransportDGFunctor
      (congrArg (fun y => chartKoszulDifferential a y l) (normalizeCoordinates_cocycle x s t))).map
        .point .point ≫ chartExteriorCochainMap a x i l (s * t) hi
          (transitionUnit_cocycle x l s t ht)
  rw [exteriorDifferentialTransportDGFunctor_map]
  exact chartExteriorCochainMap_cocycle a x i k l s t hi hs ht

end SerrePositivity.KST.DerivedBlowup
