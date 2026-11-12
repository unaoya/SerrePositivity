module
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMappingNaturality

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedInterval
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSequence

/-!
概要：基点から出る path の単体集合と終点評価の fiber 列。
方針：点つき区間からの Hom を取り、単射な端点包含に沿って制限する。
規約：path の始点を基点に固定する。終点は自由。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop のホモトピー群の次数移動。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：基点に始まる path の点つき単体集合。
方針：始点が基点の区間からの点つき Hom を取る。
規約：基点は定数 path。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の次数移動の全空間。 -/
abbrev basedPathSpace (Y : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  PointedObject.basedHom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y

/-- 概要：Kan な標的の基点始点の path space は Kan。
方針：点つき Hom の相対充填を区間へ適用する。
規約：区間自体の Kan 性は不要。
使われ方：Kerodon §3.2.5（Tag 00WD）、Goerss–Jardine I §7。fiber 列の全空間。 -/
instance basedPathSpace_kanComplex (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    KanComplex (basedPathSpace Y).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 概要：基点に始まる path の終点を評価する。
方針：点つき零次球面の端点包含で制限し、単位からの内部 Hom を標的へ同定する。
規約：通常の点つき単体集合の射。
使われ方：Kerodon §3.2.5（Tag 00WD）、Goerss–Jardine I §7。path fibration。 -/
def pathEndpoint (Y : PointedSimplicialSet.{u}) : basedPathSpace Y ⟶ Y :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint Y ≫ (MonoidalClosed.unitIsoSelf (X := Y)).hom

/-- 概要：Kan な標的の path の終点評価は Kan fibration。
方針：端点包含の単射性による制限の fibration と同型を合成する。
規約：HT-KQ は使わず相対ホーン充填のみを用いる。
使われ方：Kerodon §3.2.5（Tag 00WD）、Goerss–Jardine I §7。loop の長完全列。 -/
instance pathEndpoint_fibration (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    Fibration (pathEndpoint Y).right := by
  let e := PointedSimplicialSet.forget.mapIso (MonoidalClosed.unitIsoSelf (X := Y))
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint Y) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint Y
  change Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint Y ≫ e.hom)
  infer_instance

end

end SerrePositivity.KST.Spectra
