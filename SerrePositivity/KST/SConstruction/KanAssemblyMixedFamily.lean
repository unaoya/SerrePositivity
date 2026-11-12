module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyChoices
public import SerrePositivity.KST.SConstruction.KanAssemblyMixedChoices
public import SerrePositivity.KST.SConstruction.PointedMappingTransportUnits

/-! # 混合 Kan 延長の全パラメーター族
概要：混合選択空間を点つき写像空間へ移し、両端の射の全次数の式を示す。
方針：延長空間の射影と移送の厳密な可換式を使う。
規約：頂点の等号だけから高次の等号を推論しない。
使われ方：逆射と延長を合成する自然性の族の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra Spectra.PointedMapping

/-- 混合 Kan 延長の選択を全パラメーターで写像空間へ移す。 -/
def kanAssemblyMixedFamily (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    kanAssemblyMixedChoices r f ⟶
      (PointedObject.basedHom ((oneDirectionKanRealizationFunctor r).obj X)
        ((loopBoundaryKanFunctor (r + 1)).obj Y)).right :=
  pullback.fst
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
      ((loopBoundaryKanFunctor (r + 1)).obj Y)).right
    (SSet.yonedaEquiv.symm (familyVertex
      ((oneDirectionReducedRealizationFunctor r).map f ≫ (kanTargetAssemblyAdjointNat r).app Y)))

/-- 源の選択空間の全次数で、混合族は元の族の後合成に一致する。 -/
lemma kanAssemblyMixedFamily_source (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    kanAssemblyMixedFromSource r f ≫ kanAssemblyMixedFamily r f =
      kanAssemblyAdjointFamily r X ≫
        (PointedObject.basedHomMap ((oneDirectionKanRealizationFunctor r).obj X)
          ((loopBoundaryKanFunctor (r + 1)).map f)).right := by
  have h := pointedExtensionTransport_projection
    (PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
    ((kanTargetAssemblyAdjointNat r).app X)
    (PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
    ((oneDirectionReducedRealizationFunctor r).map f ≫ (kanTargetAssemblyAdjointNat r).app Y)
    (𝟙 _) (𝟙 _) ((loopBoundaryKanFunctor (r + 1)).map f) (by simp)
    (by rw [Category.id_comp]; exact ((kanTargetAssemblyAdjointNat r).naturality f).symm)
  exact h.trans (congrArg (kanAssemblyAdjointFamily r X ≫ ·)
    (pointedMappingTransport_source_id _))

/-- 標的の選択空間の全次数で、混合族は元の族の前合成に一致する。 -/
lemma kanAssemblyMixedFamily_target (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    kanAssemblyMixedFromTarget r f ≫ kanAssemblyMixedFamily r f =
      kanAssemblyAdjointFamily r Y ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((oneDirectionKanRealizationFunctor r).map f)
          ((loopBoundaryKanFunctor (r + 1)).obj Y)).right := by
  have h := pointedExtensionTransport_projection
    (PointedKanReplacement.unit.app (oneDirectionReducedRealization r Y))
    ((kanTargetAssemblyAdjointNat r).app Y)
    (PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
    ((oneDirectionReducedRealizationFunctor r).map f ≫ (kanTargetAssemblyAdjointNat r).app Y)
    ((oneDirectionReducedRealizationFunctor r).map f)
    ((oneDirectionKanRealizationFunctor r).map f) (𝟙 _)
    (PointedKanReplacement.unit.naturality ((oneDirectionReducedRealizationFunctor r).map f)) (by simp)
  exact h.trans (congrArg (kanAssemblyAdjointFamily r Y ≫ ·)
    (pointedMappingTransport_target_id _))

end SerrePositivity.KST.SConstruction
