module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.MapExtendDegreeNormalization
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.HomologyCoefficientClass

/-!
# 零延長と完全な係数関手の元のホモロジー同型

## 概要
零延長と完全な係数関手を交換する二つの元のホモロジー同型は一致する。

## 方針
元の核への包含と元のホモロジー射影を使って二つの合成を比較する。

## 規約
係数関手の完全性は明示的な入力であり、一般の係数拡大に仮定しない。

## 使われ方
元の多項式作用を基底へ制限する際、元のHT全複体の標準写像を保つ。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 零延長と完全な係数関手の元の指定ホモロジー同型は可換。 -/
theorem mapExtendIso_homology_compatibility
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    homologyMap (SerrePositivity.mapExtendIso F K ComplexShape.embeddingUpNat).hom (n : ℤ) ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso
          ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom ≫
        ((K.sc n).mapHomologyIso F).hom =
      (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).mapHomologyIso F).hom ≫
        F.map (K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom := by
  let e := ComplexShape.embeddingUpNat
  let KF := (F.mapHomologicalComplex (.up ℕ)).obj K
  let X := (F.mapHomologicalComplex (.up ℤ)).obj (K.extend e)
  let Y := KF.extend e
  let g := (SerrePositivity.mapExtendIso F K e).hom
  have hF : ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.iCycles n) = KF.iCycles n :=
    ShortComplex.mapCyclesIso_hom_iCycles (K.sc n) F
  have hXF : (((K.extend e).sc (e.f n)).mapCyclesIso F).hom ≫
      F.map ((K.extend e).iCycles (e.f n)) = X.iCycles (e.f n) :=
    ShortComplex.mapCyclesIso_hom_iCycles ((K.extend e).sc (e.f n)) F
  have hπF : KF.homologyπ n ≫ ((K.sc n).mapHomologyIso F).hom =
      ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.homologyπ n) :=
    coefficientHomologyIso_hom_projection (K.sc n) F
  have hπXF : X.homologyπ (e.f n) ≫
      (((K.extend e).sc (e.f n)).mapHomologyIso F).hom =
    (((K.extend e).sc (e.f n)).mapCyclesIso F).hom ≫ F.map ((K.extend e).homologyπ (e.f n)) :=
    coefficientHomologyIso_hom_projection ((K.extend e).sc (e.f n)) F
  let a := cyclesMap g (e.f n) ≫ (KF.extendCyclesIso e (j := n) (j' := (e.f n)) rfl).hom ≫
    ((K.sc n).mapCyclesIso F).hom
  let b := (((K.extend e).sc (e.f n)).mapCyclesIso F).hom ≫
    F.map (K.extendCyclesIso e (j := n) (j' := (e.f n)) rfl).hom
  have hc : a = b := by
    apply (cancel_mono (F.map (K.iCycles n))).mp
    dsimp only [a, b]
    simp only [Category.assoc]
    erw [hF, extendCyclesIso_hom_iCycles, ← Category.assoc, cyclesMap_i,
      Category.assoc, mapExtendIso_hom_f_nat]
    erw [← F.map_comp, extendCyclesIso_hom_iCycles, F.map_comp,
      ← Category.assoc, hXF]
  have hπY : Y.homologyπ (e.f n) ≫ (KF.extendHomologyIso e (j := n) rfl).hom =
      (KF.extendCyclesIso e (j := n) rfl).hom ≫ KF.homologyπ n :=
    homologyπ_extendHomologyIso_hom KF e rfl
  have hπK : (K.extend e).homologyπ (e.f n) ≫ (K.extendHomologyIso e (j := n) rfl).hom =
      (K.extendCyclesIso e (j := n) rfl).hom ≫ K.homologyπ n :=
    homologyπ_extendHomologyIso_hom K e rfl
  have hπg : X.homologyπ (e.f n) ≫ homologyMap g (e.f n) =
      cyclesMap g (e.f n) ≫ Y.homologyπ (e.f n) := homologyπ_naturality g (e.f n)
  apply (cancel_epi (X.homologyπ (e.f n))).mp
  change X.homologyπ (e.f n) ≫ homologyMap g (e.f n) ≫
      (KF.extendHomologyIso e (j := n) rfl).hom ≫ ((K.sc n).mapHomologyIso F).hom =
    X.homologyπ (e.f n) ≫ (((K.extend e).sc (e.f n)).mapHomologyIso F).hom ≫
      F.map (K.extendHomologyIso e (j := n) rfl).hom
  calc
    _ = cyclesMap g (e.f n) ≫ Y.homologyπ (e.f n) ≫
        (KF.extendHomologyIso e (j := n) rfl).hom ≫ ((K.sc n).mapHomologyIso F).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ (KF.extendHomologyIso e (j := n) rfl).hom ≫
          ((K.sc n).mapHomologyIso F).hom) hπg
    _ = a ≫ F.map (K.homologyπ n) := by
      simpa only [a, Category.assoc, hπF] using congrArg
        (fun k => cyclesMap g (e.f n) ≫ k ≫ ((K.sc n).mapHomologyIso F).hom) hπY
    _ = b ≫ F.map (K.homologyπ n) := congrArg (fun k => k ≫ F.map (K.homologyπ n)) hc
    _ = _ := by
      symm
      calc
        _ = (((K.extend e).sc (e.f n)).mapCyclesIso F).hom ≫
            F.map ((K.extend e).homologyπ (e.f n) ≫ (K.extendHomologyIso e (j := n) rfl).hom) := by
          simpa only [Category.assoc, ← F.map_comp] using congrArg
            (fun k => k ≫ F.map (K.extendHomologyIso e (j := n) rfl).hom) hπXF
        _ = b ≫ F.map (K.homologyπ n) := by
          rw [hπK, F.map_comp]
          simp only [b, Category.assoc]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
