module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HomologyAlgebraFunctor
public import SerrePositivity.EInfinity.BarrattEccles.Theory.DiscreteCoefficientOperations
public import SerrePositivity.HomologicalAlgebra.BoundedAboveExactDerived
import all SerrePositivity.EInfinity.BarrattEccles.Theory.HomologyAlgebraFunctor

/-!
# 係数制限と閉零次の類

## 概要
正確な係数制限によるホモロジーの比較を、閉零次の代表の上で計算する。

## 方針
同じ零次の元を S の単位射と T の単位射として読み、cycles と類写像を比べる。

## 規約
比較には既存の `exactCochainHomologyIso` を使う。

## 使われ方
M13 の `pi0_restrict` における単位と積の照合。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.HomologyZero

open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
open Functor.LaxMonoidal

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

local notation "R" => ScalarExtension.restriction f
local notation "M" => ModuleCat.restrictScalars f

/-- Read a unit map over T as a unit map over S. -/
def restrictionUnitMap {K : Complex T} (a : 𝟙_ (Complex T) ⟶ K) :
    𝟙_ (Complex S) ⟶ (R).obj K :=
  ε R ≫ (R).map a

/-- The two readings of a unit map give the same degree-zero element. -/
lemma restrictionUnitMap_cycle {K : Complex T} (a : 𝟙_ (Complex T) ⟶ K) :
    (cycleFromUnit ((R).obj K) (restrictionUnitMap f a)).val =
      (cycleFromUnit K a).val := by
  change a.f 0 ((ε R).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat S))).inv 1)) =
    a.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat T))).inv 1)
  rw [ScalarExtension.restriction_ε_one]

/-- Every map from the S-unit into a restricted complex comes from a T-unit map. -/
lemma restrictionUnitMap_surjective (K : Complex T) :
    Function.Surjective (restrictionUnitMap f (K := K)) := by
  intro a
  let x := cycleFromUnit ((R).obj K) a
  let y : zeroCycles K := ⟨x.val, x.property⟩
  refine ⟨unitFromCycle K y, (unitCycleEquiv ((R).obj K)).injective (Subtype.ext ?_)⟩
  change (cycleFromUnit ((R).obj K) (restrictionUnitMap f (unitFromCycle K y))).val = x.val
  rw [restrictionUnitMap_cycle, cycleFromUnit_unitFromCycle]

/-- The canonical homology comparison sends the class of a restricted unit map
to the original class. -/
lemma restrictionUnitMap_class {K : Complex T} (a : 𝟙_ (Complex T) ⟶ K) :
    ((exactCochainHomologyIso M 0).hom.app K)
      (_root_.SerrePositivity.HomologyZero.unitClass ((R).obj K) (restrictionUnitMap f a)) = _root_.SerrePositivity.HomologyZero.unitClass K a := by
  let x := cycleFromUnit ((R).obj K) (restrictionUnitMap f a)
  let y := cycleFromUnit K a
  let c : ((R).obj K).cycles 0 ⟶ (M).obj (K.cycles 0) := ((K.sc 0).mapCyclesIso M).hom
  let e : ((R).obj K).homology 0 ⟶ (M).obj (K.homology 0) := ((K.sc 0).mapHomologyIso M).hom
  have hi : c ≫ (M).map (K.iCycles 0) = ((R).obj K).iCycles 0 :=
    (K.sc 0).mapCyclesIso_hom_iCycles M
  have hπ : ((R).obj K).homologyπ 0 ≫ e = c ≫ (M).map (K.homologyπ 0) := by
    let d := (K.sc 0).leftHomologyData
    change ((K.sc 0).map M).homologyπ ≫ ((K.sc 0).mapHomologyIso M).hom =
      ((K.sc 0).mapCyclesIso M).hom ≫ (M).map (K.sc 0).homologyπ
    rw [d.mapHomologyIso_eq M, d.mapCyclesIso_eq M]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc,
      ShortComplex.LeftHomologyData.map_π, ← Functor.map_comp,
      ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
  have hc : c ((actualCycles ((R).obj K)).hom x) = (actualCycles K).hom y := by
    apply (ModuleCat.mono_iff_injective ((M).map (K.iCycles 0))).mp inferInstance
    change ((M).map (K.iCycles 0)) (c ((actualCycles ((R).obj K)).hom x)) =
      K.iCycles 0 ((actualCycles K).hom y)
    calc
      _ = ((R).obj K).iCycles 0 ((actualCycles ((R).obj K)).hom x) :=
        congrArg (fun m => m ((actualCycles ((R).obj K)).hom x)) hi
      _ = x.val := congrArg (fun m => m x) (actualCycles_i ((R).obj K))
      _ = y.val := restrictionUnitMap_cycle f a
      _ = _ := (congrArg (fun m => m y) (actualCycles_i K)).symm
  change e ((ModuleCat.ofHom (_root_.SerrePositivity.HomologyZero.classMap ((R).obj K))) x) =
    (ModuleCat.ofHom (_root_.SerrePositivity.HomologyZero.classMap K)) y
  rw [← actualCycles_π, ← actualCycles_π]
  change (((R).obj K).homologyπ 0 ≫ e) ((actualCycles ((R).obj K)).hom x) =
    K.homologyπ 0 ((actualCycles K).hom y)
  rw [hπ]
  exact congrArg (fun z => (M).map (K.homologyπ 0) z) hc

end SerrePositivity.EInfinity.HomologyZero
