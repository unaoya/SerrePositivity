module
public import SerrePositivity.KST.ProExcision.RelativeModuleSequentialColimit
public import SerrePositivity.KST.ProExcision.RelativeModuleDiagramMaps

/-!
# 実相対商と順序余極限の比較の自然性

概要：実正方形から得る相対写像が、実相対商と余極限の比較同型に可換であることを示す。
方針：通常商射影の全射性と余核の実普遍性を使い、商の前の実正方形へ帰着する。
規約：KST Proposition 4.14、SW92 Lemma 1.4。使われ方：実安定相対零化の移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u r
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits
variable {R : Type r} [Ring R] {A B A' B' : ℕ ⥤ ModuleCat.{u} R}

/-- 概要：実相対商と余極限の比較は実通常商射影と整合する。
方針：二つの実余核余錐の普遍同型の標準射との可換性を使う。
規約：SW92 Lemma 1.4。使われ方：実比較同型の自然性。 -/
lemma relativeModuleSequentialColimitIso_projection (f : A ⟶ B) :
    ModuleCat.ofHom (colimMap f).hom.range.mkQ ≫ (relativeModuleSequentialColimitIso f).hom =
      colimMap (relativeModuleDiagramProjection f) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (ModuleCat.cokernelIsColimit (colimMap f))
    ((relativeModuleDiagramCofork f).mapIsColimit (relativeModuleDiagramIsCokernel f)
      (colim : (ℕ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R)) WalkingParallelPair.one

/-- 概要：実加群図式の正方形が余極限の実相対商に誘導する実写像。
方針：実余極限関手を正方形へ適用し、実像の商へ降ろす。
規約：KST Proposition 4.14。使われ方：安定相対写像と有限 rank の比較。 -/
def relativeModuleSequentialMap {f : A ⟶ B} {f' : A' ⟶ B'}
    (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    relativeModule (colimMap f) ⟶ relativeModule (colimMap f') :=
  relativeModuleMap _ _ (colimMap a) (colimMap b) (by
    change colim.map f ≫ colim.map b = colim.map a ≫ colim.map f'
    rw [← colim.map_comp, ← colim.map_comp, h])

/-- 概要：実相対商と順序余極限の比較同型は実正方形からの写像に自然。
方針：実通常商射影を前合成し、射影との整合と実余極限関手の合成保存を使う。
規約：KST Proposition 4.14、SW92 Lemma 1.4。
使われ方：有限 rank の実相対零化を実安定相対写像へ移す。 -/
lemma relativeModuleSequentialColimitIso_natural {f : A ⟶ B} {f' : A' ⟶ B'}
    (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    relativeModuleSequentialMap a b h ≫ (relativeModuleSequentialColimitIso f').hom =
      (relativeModuleSequentialColimitIso f).hom ≫ colimMap (relativeModuleDiagramMap a b h) := by
  have : Epi (ModuleCat.ofHom (colimMap f).hom.range.mkQ) :=
    (ModuleCat.epi_iff_range_eq_top _).mpr (Submodule.range_mkQ _)
  apply (cancel_epi (ModuleCat.ofHom (colimMap f).hom.range.mkQ)).1
  calc
    ModuleCat.ofHom (colimMap f).hom.range.mkQ ≫
        (relativeModuleSequentialMap a b h ≫ (relativeModuleSequentialColimitIso f').hom) =
      colimMap b ≫ (ModuleCat.ofHom (colimMap f').hom.range.mkQ ≫
        (relativeModuleSequentialColimitIso f').hom) := by
      unfold relativeModuleSequentialMap
      rw [← Category.assoc, relativeModuleMap_projection, Category.assoc]
    _ = colimMap b ≫ colimMap (relativeModuleDiagramProjection f') := by
      rw [relativeModuleSequentialColimitIso_projection]
    _ = colimMap (relativeModuleDiagramProjection f) ≫ colimMap (relativeModuleDiagramMap a b h) := by
      change colim.map b ≫ colim.map (relativeModuleDiagramProjection f') =
        colim.map (relativeModuleDiagramProjection f) ≫ colim.map (relativeModuleDiagramMap a b h)
      rw [← colim.map_comp, ← colim.map_comp, relativeModuleDiagramMap_projection]
    _ = ModuleCat.ofHom (colimMap f).hom.range.mkQ ≫
        ((relativeModuleSequentialColimitIso f).hom ≫ colimMap (relativeModuleDiagramMap a b h)) := by
      rw [← Category.assoc, relativeModuleSequentialColimitIso_projection]

end SerrePositivity.KST.ProExcision
