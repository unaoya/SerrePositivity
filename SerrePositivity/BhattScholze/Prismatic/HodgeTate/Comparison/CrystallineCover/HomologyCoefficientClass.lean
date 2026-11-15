module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension

/-!
# 係数ホモロジー同型の元の類への正規化

## 概要
元の核・余核から作るホモロジー同型を、同じ余輪体の射影で計算する。

## 方針
保存した左ホモロジーデータの核・射影の二つの標準式を合成する。

## 規約
同型を任意に選ばず、元の mapHomologyIso を使う。

## 使われ方
特定の Zp 係数変更のホモロジー同型が、同じ標準 HT 類を運ぶことの照合。
-/

public noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type u} {D : Type v} [Category C] [Category D]
variable [HasZeroMorphisms C] [HasZeroMorphisms D]
variable (S : ShortComplex C) [S.HasHomology] (F : C ⥤ D) [F.PreservesZeroMorphisms]
variable [F.PreservesLeftHomologyOf S] [(S.map F).HasHomology]

/-- 元のホモロジー同型は、元の余輪体から類への射影を保つ。 -/
@[reassoc] theorem coefficientHomologyIso_hom_projection :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, (h.map F).homologyπ_comp_homologyIso_hom]
  simp only [Category.assoc]
  change (h.map F).cyclesIso.hom ≫ F.map h.π ≫ F.map h.homologyIso.inv = _
  simp only [Category.assoc, ← F.map_comp, h.π_comp_homologyIso_inv]

/-- 逆向きの元の係数ホモロジー同型も、同じ余輪体の射影で計算する。 -/
@[reassoc] theorem coefficientHomologyIso_inv_projection :
    F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ := by
  apply (cancel_mono (S.mapHomologyIso F).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    coefficientHomologyIso_hom_projection, Iso.inv_hom_id_assoc]

/-- 元の核の係数同型は、元の余輪体の包含を保つ。 -/
@[reassoc] theorem coefficientCyclesIso_inv_inclusion :
    (S.mapCyclesIso F).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
  rw [← ShortComplex.mapCyclesIso_hom_iCycles S F, Iso.inv_hom_id_assoc]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
