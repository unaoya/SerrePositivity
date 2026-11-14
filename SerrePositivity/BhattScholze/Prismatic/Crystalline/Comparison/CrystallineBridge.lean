module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallineDivisionEnvelope
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechSource
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel

/-!
# Frobenius に沿う結晶の橋

## 概要
affine Čech–Alexander 模型から結晶の完備 p 除算模型へ、Frobenius を延長する
（BS 著者版 Theorem 5.2 の結晶比較の橋）。

## 方針
差の Frobenius 像が p で割り切れるので、envelope の普遍性で射を作る。

## 規約
始域の選択生成元は終域の p に送る。

## 使われ方
mod p の結晶比較と Bockstein の照合。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "Z" => (crystallineBasePrism p)
local notation "hZ" => crystallineBaseBounded p
local notation "B" n => completedFreeDelta Z (AffineIndex r (SimplexCategory.len n))
local notation "D" n => completedFreeDeltaStructure Z (AffineIndex r (SimplexCategory.len n))
local notation "β" n => completedFreeDeltaBase Z (AffineIndex r (SimplexCategory.len n))

/-- 結晶基底上の Čech–Alexander 模型の台環。 -/
abbrev zpCech := htRings (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r

private abbrev aff (n : SimplexCategory) :=
  affineEnvelopeTerm (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r n.len
    (polyCutoff Z r) le_rfl

private abbrev targetPrism (n : SimplexCategory) :=
  crystallineDivisionPrism (D n) (crystallinePDDifference.{u} p r n)

private def targetIdeal (n : SimplexCategory) : Ideal ((pdDeltaRings.{u} p r).obj n) :=
  (targetPrism.{u} p r n).ideal

private theorem targetIdeal_eq (n : SimplexCategory) :
    targetIdeal.{u} p r n = Ideal.span {(p : (pdDeltaRings.{u} p r).obj n)} :=
  congrArg (fun x : (pdDeltaRings.{u} p r).obj n => Ideal.span {x})
    (crystallineDivisionPrism_generator (D n) (crystallinePDDifference p r n))

private def toTarget (n : SimplexCategory) :
    (B n) →+* (pdDeltaRings.{u} p r).obj n :=
  (pdDeltaUnit p r n).comp (D n).frobeniusLift

private theorem toTarget_isDeltaHom (n : SimplexCategory) :
    (D n).IsDeltaHom (targetPrism.{u} p r n).deltaStructure (toTarget.{u} p r n) := by
  rw [crystallineDivisionPrism_deltaStructure]
  exact (pdDeltaUnit_isDeltaHom p r n).comp
    (frobeniusLift_isDeltaHom_of_regular (D n)
      (crystallineCompletedFreeDelta_primeRegular p (AffineIndex r n.len)))

private theorem toTarget_generator (n : SimplexCategory) :
    toTarget.{u} p r n ((β n) (Z).generator) = (p : (pdDeltaRings.{u} p r).obj n) := by
  rw [crystallineBase_generator, map_natCast, map_natCast]

private theorem toTarget_ideal (n : SimplexCategory) :
    (affineDifferenceIdeal Z r n.len).map (toTarget.{u} p r n) ≤ targetIdeal.{u} p r n := by
  rw [targetIdeal_eq]
  rw [Ideal.map_le_iff_le_comap, affineDifferenceIdeal, Ideal.span_le]
  rintro x (hx | ⟨⟨j,i⟩, rfl⟩)
  · change toTarget p r n x ∈ (Ideal.span {(p : (pdDeltaRings.{u} p r).obj n)} : Ideal ((pdDeltaRings.{u} p r).obj n))
    rw [show x = (β n) (Z).generator from hx, toTarget_generator]
    exact Ideal.subset_span rfl
  · change toTarget p r n
      (affineVariable Z r n.len j i - affineVariable Z r n.len j 0) ∈
      (Ideal.span {(p : (pdDeltaRings.{u} p r).obj n)} : Ideal ((pdDeltaRings.{u} p r).obj n))
    rw [Ideal.mem_span_singleton]
    exact ⟨divideCopy p r n j i, (divideCopy_spec p r n j i).symm⟩

private theorem bridgeApp_existsUnique (n : SimplexCategory) :
    ∃! f : (zpCech.{u} p r).obj n →+* (pdDeltaRings.{u} p r).obj n,
      (aff p r n).X.Q.deltaStructure.IsDeltaHom (targetPrism.{u} p r n).deltaStructure f ∧
        f.comp (aff p r n).η = toTarget p r n := by
  refine (aff p r n).envelope.lift (targetPrism p r n) (toTarget p r n)
    (toTarget_isDeltaHom p r n) ?_ (toTarget_ideal p r n)
  change Ideal.span {(Z).generator} ≤
    (targetPrism p r n).ideal.comap ((toTarget p r n).comp (β n))
  rw [Ideal.span_singleton_le_iff_mem]
  change toTarget p r n ((β n) (Z).generator) ∈ (targetPrism p r n).ideal
  rw [toTarget_generator]
  exact (crystallineDivisionPrism_generator (D n) (crystallinePDDifference p r n) ▸
    (Ideal.subset_span (Set.mem_singleton (targetPrism p r n).generator)))

private def bridgeApp (n : SimplexCategory) :
    (zpCech.{u} p r).obj n →+* (pdDeltaRings.{u} p r).obj n :=
  (bridgeApp_existsUnique p r n).choose

private theorem bridgeApp_spec (n : SimplexCategory) :
    (aff p r n).X.Q.deltaStructure.IsDeltaHom (targetPrism.{u} p r n).deltaStructure
      (bridgeApp.{u} p r n) ∧
      (bridgeApp.{u} p r n).comp (aff p r n).η = toTarget p r n :=
  (bridgeApp_existsUnique p r n).choose_spec.1

private theorem affineUnit_nat {m n : SimplexCategory} (θ : m ⟶ n) :
    ((zpCech.{u} p r).map θ).hom.comp (aff p r m).η =
      (aff p r n).η.comp (crystallineCechSourceMap p r θ) := by
  let X := aff.{u} p r m
  let Y := aff.{u} p r n
  let f := affineTermMap Z X Y θ
  let g := crystallineCechSourceMap.{u} p r θ
  change f.toHom.toRingHom.comp X.η = Y.η.comp g
  apply completedFreeDeltaHom_ext Z (AffineIndex r m.len) Y.X.Q.deltaStructure
    Y.X.toHom.toRingHom Y.X.toHom.map_delta Y.X.Q.complete_p
    Y.X.toHom.isModuleComplete_map_generator
    (f.toHom.map_delta.comp X.envelope.isDeltaHom)
    (Y.envelope.isDeltaHom.comp (crystallineCechSourceMap_spec p r θ).1)
  · rw [RingHom.comp_assoc, X.base_eq]
    exact congrArg OrientedPrism.Hom.toRingHom f.comm_base
  · rw [RingHom.comp_assoc, (crystallineCechSourceMap_spec p r θ).2.1, Y.base_eq]
  · rintro ⟨⟨j,i⟩⟩
    exact (affineTermMap_apply Z X Y θ j i).trans
      (congrArg Y.η ((crystallineCechSourceMap_spec p r θ).2.2 ⟨(j,i)⟩)).symm

private theorem targetMap_isDeltaHom {m n : SimplexCategory} (θ : m ⟶ n) :
    (targetPrism.{u} p r m).deltaStructure.IsDeltaHom (targetPrism.{u} p r n).deltaStructure
      ((pdDeltaRings.{u} p r).map θ).hom := by
  rw [crystallineDivisionPrism_deltaStructure, crystallineDivisionPrism_deltaStructure]
  exact (pdDeltaMap_spec p r θ).1

private theorem toTarget_nat {m n : SimplexCategory} (θ : m ⟶ n) :
    ((pdDeltaRings.{u} p r).map θ).hom.comp (toTarget p r m) =
      (toTarget p r n).comp (crystallineCechSourceMap p r θ) := by
  change (pdDeltaMap p r θ).comp ((pdDeltaUnit p r m).comp (D m).frobeniusLift) = _
  rw [← RingHom.comp_assoc, (pdDeltaMap_spec p r θ).2, RingHom.comp_assoc]
  apply RingHom.ext
  intro x
  exact congrArg (pdDeltaUnit p r n)
    ((crystallineCechSourceMap_spec p r θ).1.map_frobeniusLift x)

/-- affine Čech–Alexander 模型から結晶側模型への Frobenius の橋。 -/
def crystallineBridge : zpCech.{u} p r ⟶ pdDeltaRings.{u} p r where
  app n := CommRingCat.ofHom (bridgeApp p r n)
  naturality m n θ := by
    apply CommRingCat.hom_ext
    let f := ((zpCech.{u} p r).map θ).hom
    let g := ((pdDeltaRings.{u} p r).map θ).hom
    let M := aff.{u} p r m
    let N := aff.{u} p r n
    let z := (toTarget.{u} p r n).comp (crystallineCechSourceMap p r θ)
    have hz : (D m).IsDeltaHom (targetPrism.{u} p r n).deltaStructure z :=
      (toTarget_isDeltaHom p r n).comp (crystallineCechSourceMap_spec p r θ).1
    have h₁ : (g.comp (bridgeApp p r m)).comp M.η = z := by
      calc
        _ = g.comp ((bridgeApp p r m).comp M.η) := RingHom.comp_assoc _ _ _
        _ = g.comp (toTarget p r m) :=
          congrArg (fun k => g.comp k) (bridgeApp_spec p r m).2
        _ = _ := toTarget_nat p r θ
    have h₂ : ((bridgeApp p r n).comp f).comp M.η = z := by
      calc
        _ = (bridgeApp p r n).comp (f.comp M.η) := RingHom.comp_assoc _ _ _
        _ = (bridgeApp p r n).comp (N.η.comp (crystallineCechSourceMap p r θ)) :=
          congrArg (fun k => (bridgeApp p r n).comp k) (affineUnit_nat p r θ)
        _ = ((bridgeApp p r n).comp N.η).comp (crystallineCechSourceMap p r θ) :=
          (RingHom.comp_assoc _ _ _).symm
        _ = _ := congrArg (fun k => k.comp (crystallineCechSourceMap p r θ))
          (bridgeApp_spec p r n).2
    have hgQ : (targetIdeal.{u} p r m).map g ≤ targetIdeal.{u} p r n := by
      rw [targetIdeal_eq, targetIdeal_eq, Ideal.map_span, Set.image_singleton, map_natCast]
    have hzEq : z = g.comp (toTarget p r m) := (toTarget_nat p r θ).symm
    have hI : (affineDifferenceIdeal Z r m.len).map z ≤ targetIdeal.{u} p r n := by
      rw [hzEq, ← Ideal.map_map]
      exact (Ideal.map_mono (toTarget_ideal p r m)).trans hgQ
    have hbase : (Z).ideal ≤ (targetIdeal.{u} p r n).comap (z.comp (β m)) := by
      change Ideal.span {(Z).generator} ≤ _
      rw [Ideal.span_singleton_le_iff_mem]
      change z ((β m) (Z).generator) ∈ targetIdeal.{u} p r n
      exact hI (Ideal.mem_map_of_mem _ (Ideal.subset_span
        (Set.mem_insert _ _)))
    obtain ⟨h, _, hu⟩ := M.envelope.lift (targetPrism p r n) z hz hbase hI
    change (bridgeApp p r n).comp f = g.comp (bridgeApp p r m)
    exact (hu _ ⟨(bridgeApp_spec p r n).1.comp (affineTermMap Z M N θ).toHom.map_delta, h₂⟩).trans
      (hu _ ⟨(targetMap_isDeltaHom p r θ).comp (bridgeApp_spec p r m).1, h₁⟩).symm

theorem crystallineBridge_generator (n : SimplexCategory) :
    (crystallineBridge.{u} p r).app n
      (htGenerator (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r n) =
      (p : (pdDeltaRings.{u} p r).obj n) := by
  change bridgeApp p r n ((aff p r n).X.toHom.toRingHom (Z).generator) = _
  rw [← DFunLike.congr_fun (aff p r n).base_eq (Z).generator]
  exact (DFunLike.congr_fun (bridgeApp_spec p r n).2 ((β n) (Z).generator)).trans
    (toTarget_generator p r n)

/-- 結晶の橋を各項で p により割る。 -/
abbrev crystallineBridgeModP :
    reducedModel (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r ⟶
      modPrimeCosimplicial p (pdDeltaRings.{u} p r) :=
  quotPowMap (zpCech p r) (htGenerator _ _ r) (htGenerator_nat _ _ r)
    (fun n => (p : (pdDeltaRings p r).obj n)) (fun θ => map_natCast ((pdDeltaRings p r).map θ).hom p)
    (crystallineBridge p r) (crystallineBridge_generator p r) 1

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 5.2" (partial := component) "結晶の橋の mod p のコホモロジー同型（有限変数・I＝(p)）。比較同型そのものは D68 の段 3 と結晶サイト（a1-design §11） ／ 11-10 更新。整係数の版と W(C)・J の多項式の版（Thm 6.4 で使う形）も本体 ／ 11-12 夜更新（§5・§6 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.crystallineBridge
