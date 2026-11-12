module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFArrowStages
public import SerrePositivity.KST.SConstruction.KStageHomotopyFunctor

/-!
概要：同じ有限 native 射について旧 BF 正段と実 BF 正段の指定比較を可換にする。
方針：元射影の成分自然性と、同じ実帰納比較の厳密自然性を合成する。
規約：全スペクトル写像空間での比較を使わない。使われ方：新旧四辺の全整数群作用。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open NonConnective Spectra
open Fibration PointedMapping
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

local instance nativeBFArrowNaturalityTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 概要：同じ実帰納比較は元境界商射と実 BF 正段射に厳密に自然。
方針：全 Hom 自然性を同じ通常射に評価する。
規約：全正段で同じ比較成分。使われ方：旧正段との比較の合成。 -/
lemma dgKappaNativeBFFinitePositiveComparison_naturality
    {C E : DGKappaNativeBFFiniteInput.{u, v} R D I} (f : C ⟶ E) (r : ℕ) :
    (exInfinityPointedKanMap
      (boundaryReducedRealizationMap r (stableExactInputMap f.hom))).hom ≫
        (dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).comparison E =
      (dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).comparison C ≫
        (dgKappaNativeBFFiniteArrow.{u, v} R D I f).app (r + 1) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap_naturality
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r)
    (dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I (r + 1))
    (dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).comparison
    (dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).naturality f
  rw [dgKappaNativeBFFiniteBoundaryFunctor_hom, dgKappaNativeBFFiniteArrow_app] at h
  exact h

/-- 概要：旧 BF 射と同じ実 BF 射は指定正段比較で基点固定成分が可換。
方針：元 SOA 射影・Ex∞ 比較の自然性の後に同じ厳密帰納比較を合成する。
規約：正段ごとの同じ実射。使われ方：全整数群の可換性。 -/
lemma dgKappaNativeBFPositiveLevelComparison_naturality_component
    {C E : DGKappaNativeBFFiniteInput.{u, v} R D I} (f : C ⟶ E) (r : ℕ) :
    componentOf ((kSpectrumMap (stableExactInputMap f.hom)).app (r + 1) ≫
      dgKappaNativeBFPositiveLevelComparison.{u, v} R D I E r) =
      componentOf (dgKappaNativeBFPositiveLevelComparison.{u, v} R D I C r ≫
        (dgKappaNativeBFFiniteArrow.{u, v} R D I f).app (r + 1)) := by
  let q := stableExactInputMap f.hom
  let pC := (monicKKanSequenceProjection (sInputModel C.obj)).app (r + 1)
  let pE := (monicKKanSequenceProjection (sInputModel E.obj)).app (r + 1)
  let cC := pointedSOAExInfinityComparison (stableBoundaryPointedObject r C.obj)
  let cE := pointedSOAExInfinityComparison (stableBoundaryPointedObject r E.obj)
  let b := boundaryReducedRealizationMap r q
  let tC := (dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).comparison C
  let tE := (dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).comparison E
  have h₁ := componentOf_comp_right
    (monicKKanSequenceMap_projection_component q (r + 1)) (cE ≫ tE)
  have h₂ := componentOf_comp_left
    (componentOf_comp_right (pointedSOAExInfinityComparison_naturality_component b).symm tE) pC
  have ht := dgKappaNativeBFFinitePositiveComparison_naturality.{u, v} R D I f r
  change componentOf ((kSpectrumMap q).app (r + 1) ≫ pE ≫ cE ≫ tE) =
    componentOf ((pC ≫ cC ≫ tC) ≫
      (dgKappaNativeBFFiniteArrow.{u, v} R D I f).app (r + 1))
  have h₁' : componentOf ((kSpectrumMap q).app (r + 1) ≫ pE ≫ cE ≫ tE) =
      componentOf (pC ≫ PointedKanReplacement.map b ≫ cE ≫ tE) := by
    exact (congrArg componentOf (Category.assoc ((kSpectrumMap q).app (r + 1))
      pE (cE ≫ tE))).symm.trans (h₁.trans
        (congrArg componentOf (Category.assoc pC (PointedKanReplacement.map b) (cE ≫ tE))))
  have h₂' : componentOf (pC ≫ PointedKanReplacement.map b ≫ cE ≫ tE) =
      componentOf (pC ≫ cC ≫ (exInfinityPointedKanMap b).hom ≫ tE) := by
    exact (congrArg (fun k => componentOf (pC ≫ k))
      (Category.assoc (PointedKanReplacement.map b) cE tE)).symm.trans
      (h₂.trans (congrArg (fun k => componentOf (pC ≫ k))
        (Category.assoc cC (exInfinityPointedKanMap b).hom tE)))
  exact h₁'.trans (h₂'.trans (congrArg componentOf
    ((congrArg (fun k => pC ≫ cC ≫ k) ht).trans
      (Category.assoc pC cC _).symm |>.trans (Category.assoc (pC ≫ cC) tC _).symm)))

/-- 概要：指定整数群比較は同じ正段の基点固定写像。
方針：標準正段の正次数準同型を評価する。
規約：同じ指定比較。使われ方：全整数自然性の計算。 -/
lemma dgKappaNativeBFIntegerComparison_apply
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup (kOmegaSpectrum (sInputModel C.obj)) j) :
    dgKappaNativeBFIntegerComparison.{u, v} R D I C j a =
      pointedHomotopyMap (OmegaSpectrum.degree j (OmegaSpectrum.canonicalLevel j))
        (dgKappaNativeBFPositiveLevelComparison.{u, v} R D I C j.natAbs) a :=
  OmegaSpectrum.positiveLevelMap_apply _ _ _ _ _ _ _

/-- 概要：同じ実 BF 射と旧 K 射は指定全整数群同型で可換。
方針：標準正段の成分自然性を同じ正次数のホモトピー群へ送る。
規約：全整数次数。使われ方：K-B・K-cof への新四辺の作用の接続。 -/
lemma dgKappaNativeBFIntegerComparison_naturality
    {C E : DGKappaNativeBFFiniteInput.{u, v} R D I} (f : C ⟶ E) (j : ℤ) :
    (OmegaSpectrum.homotopyMap (dgKappaNativeBFFiniteArrow.{u, v} R D I f) j).comp
        (dgKappaNativeBFIntegerComparison.{u, v} R D I C j) =
      (dgKappaNativeBFIntegerComparison.{u, v} R D I E j).comp
        (OmegaSpectrum.homotopyMap (kSpectrumMap (stableExactInputMap f.hom)) j) := by
  apply MonoidHom.ext
  intro a
  change OmegaSpectrum.homotopyMap (dgKappaNativeBFFiniteArrow.{u, v} R D I f) j
    (dgKappaNativeBFIntegerComparison.{u, v} R D I C j a) =
      dgKappaNativeBFIntegerComparison.{u, v} R D I E j
        (OmegaSpectrum.homotopyMap (kSpectrumMap (stableExactInputMap f.hom)) j a)
  let n := OmegaSpectrum.degree j (OmegaSpectrum.canonicalLevel j)
  let cC := dgKappaNativeBFPositiveLevelComparison.{u, v} R D I C j.natAbs
  let cE := dgKappaNativeBFPositiveLevelComparison.{u, v} R D I E j.natAbs
  let g := (dgKappaNativeBFFiniteArrow.{u, v} R D I f).app (j.natAbs + 1)
  let q := (kSpectrumMap (stableExactInputMap f.hom)).app (j.natAbs + 1)
  have hl := (OmegaSpectrum.homotopyMap_apply
    (dgKappaNativeBFFiniteArrow.{u, v} R D I f) j
    (dgKappaNativeBFIntegerComparison.{u, v} R D I C j a)).trans
      (congrArg (pointedHomotopyMap n g)
        (dgKappaNativeBFIntegerComparison_apply.{u, v} R D I C j a))
  have hr := (dgKappaNativeBFIntegerComparison_apply.{u, v} R D I E j
    (OmegaSpectrum.homotopyMap (kSpectrumMap (stableExactInputMap f.hom)) j a)).trans
      (congrArg (pointedHomotopyMap n cE)
        (OmegaSpectrum.homotopyMap_apply (kSpectrumMap (stableExactInputMap f.hom)) j a))
  have hm := (pointedHomotopyMap_comp n cC g a).symm.trans
    ((congrFun (pointedHomotopyMap_eq_of_component
      (dgKappaNativeBFPositiveLevelComparison_naturality_component.{u, v}
        R D I f j.natAbs).symm n) a).trans (pointedHomotopyMap_comp n q cE a))
  exact hl.trans (hm.trans hr.symm)

end SerrePositivity.KST.SConstruction
