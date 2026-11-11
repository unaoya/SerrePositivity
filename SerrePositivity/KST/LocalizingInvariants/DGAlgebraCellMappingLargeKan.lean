module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingKanFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Kan
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UniverseKanPullback

/-!
概要：native cell 写像の Kan 模型を、代数の ∞ 局所化の写像空間と同じ宇宙に持ち上げる。
方針：元の全単体集合に ULift を適用し、全標的射と元の代数表示を保持する。
規約：Kan 性は F1 の既存の宇宙移送を使い、モデル構造を入力しない。
使われ方：元の dg 代数の大きい nerve と導来写像空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

def multiplicativeCellMappingLargeKanFunctor : Mon (Complex R) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1} where
  obj B := ⟨SSet.uliftFunctor.{u + 1, u}.obj
    (multiplicativeMappingSimplices R (cellResolution R A) B), inferInstance⟩
  map f := SSet.uliftFunctor.{u + 1, u}.map
    (multiplicativeMappingPostcompose R (cellResolution R A) f)
  map_id B := (multiplicativeMappingFunctor R (cellResolution R A) ⋙
    SSet.uliftFunctor.{u + 1, u}).map_id B
  map_comp f g := (multiplicativeMappingFunctor R (cellResolution R A) ⋙
    SSet.uliftFunctor.{u + 1, u}).map_comp f g

lemma multiplicativeCellMappingLargeKanFunctor_forget :
    multiplicativeCellMappingLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget =
      multiplicativeMappingFunctor R (cellResolution R A) ⋙ SSet.uliftFunctor.{u + 1, u} := rfl

set_option maxHeartbeats 800000 in -- 元の写像関手と ULift の二段の錐を同定する。
def multiplicativeCellMappingLargeKanCone_underlying_isLimit
    (F : WalkingCospan ⥤ Mon (Complex R))
    (c : Cone F) (hc : IsLimit c) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone
      ((multiplicativeCellMappingLargeKanFunctor R A).mapCone c)) := by
  change IsLimit ((multiplicativeCellMappingLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).mapCone c)
  rw [multiplicativeCellMappingLargeKanFunctor_forget]
  have := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.uliftFunctor_preservesCospanLimits.{u, u + 1}
  exact isLimitOfPreserves
    (multiplicativeMappingFunctor R (cellResolution R A) ⋙ SSet.uliftFunctor.{u + 1, u}) hc

def multiplicativeCellMappingInfinityKanFunctor : InfinityPresentation R ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1} :=
  ULiftHom.down ⋙ multiplicativeCellMappingLargeKanFunctor R A

lemma multiplicativeCellMappingInfinityKanFunctor_original :
    infinityPresentationFunctor R ⋙ multiplicativeCellMappingInfinityKanFunctor R A =
      multiplicativeCellMappingLargeKanFunctor R A := by
  have hud : (ULiftHom.up : Mon (Complex R) ⥤ InfinityPresentation R) ⋙
      ULiftHom.down = 𝟭 _ := rfl
  change ULiftHom.up ⋙ (ULiftHom.down ⋙ multiplicativeCellMappingLargeKanFunctor R A) = _
  rw [← Functor.assoc, hud, Functor.id_comp]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
