module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.HomologyCoefficientClass

/-!
# 元のホモロジー係数同型の合成

## 概要
同じ余輪体の包含と類への射影を保つ係数同型は、関手の合成について整合する。

## 方針
核への包含の単射性とホモロジー射影の全射性で二つの合成を比較する。

## 規約
必要なホモロジーの保存を個別に仮定する。任意の係数拡大の完全性は仮定しない。

## 使われ方
零微分の形式模型における通常底変換のホモロジー単位の同型性。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable (K : ShortComplex (ModuleCat.{u} R))
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) (G : ModuleCat.{u} S ⥤ ModuleCat.{u} T)
variable [F.Additive] [G.Additive] [G.PreservesMonomorphisms]
variable [F.PreservesLeftHomologyOf K] [G.PreservesLeftHomologyOf (K.map F)]
variable [(F ⋙ G).PreservesLeftHomologyOf K]

/-- 元の余輪体同型は、同じ二つの係数関手の合成と可換。 -/
theorem coefficientCyclesIso_comp_hom :
    (K.mapCyclesIso (F ⋙ G)).hom =
      ((K.map F).mapCyclesIso G).hom ≫ G.map (K.mapCyclesIso F).hom := by
  have hi : F.map K.iCycles = (K.mapCyclesIso F).inv ≫ (K.map F).iCycles := by
    rw [← ShortComplex.mapCyclesIso_hom_iCycles K F, Iso.inv_hom_id_assoc]
  haveI : Mono (F.map K.iCycles) := by rw [hi]; infer_instance
  apply (cancel_mono (G.map (F.map K.iCycles))).mp
  change (K.mapCyclesIso (F ⋙ G)).hom ≫ (F ⋙ G).map K.iCycles = _
  rw [ShortComplex.mapCyclesIso_hom_iCycles]
  simp only [Category.assoc, ← G.map_comp, ShortComplex.mapCyclesIso_hom_iCycles]
  rfl

/-- 元のホモロジー係数同型は、同じ二つの係数関手の合成と可換。 -/
theorem coefficientHomologyIso_comp_hom :
    (K.mapHomologyIso (F ⋙ G)).hom =
      ((K.map F).mapHomologyIso G).hom ≫ G.map (K.mapHomologyIso F).hom := by
  apply (cancel_epi (K.map (F ⋙ G)).homologyπ).mp
  rw [coefficientHomologyIso_hom_projection]
  change (K.mapCyclesIso (F ⋙ G)).hom ≫ G.map (F.map K.homologyπ) =
    ((K.map F).map G).homologyπ ≫ ((K.map F).mapHomologyIso G).hom ≫
      G.map (K.mapHomologyIso F).hom
  rw [coefficientHomologyIso_hom_projection_assoc]
  rw [← G.map_comp, coefficientHomologyIso_hom_projection]
  simp only [G.map_comp, ← Category.assoc]
  rw [← coefficientCyclesIso_comp_hom]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
