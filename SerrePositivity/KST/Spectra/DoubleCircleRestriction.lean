module

public import SerrePositivity.KST.Spectra.CircleMappingComponents
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism

/-!
概要：二つの Kan 円を源とする写像空間を通常の二つの円へ制限する。
方針：円の anodyne 置換による源の制限と内部 Hom の標的の置換不変性を合成する。
規約：実際の反復内部 Hom の射を使う。
使われ方：Goerss–Jardine I §7、BF 1978 §2。三角形による変数交換を Kan 円の模型へ移す。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：二つの Kan 円の写像を二つの通常の円へ制限する点つき射。
方針：外側の源を制限してから内側の源の制限を後合成する。
規約：円の Kan 置換の標準の射を両変数で使う。
使われ方：Goerss–Jardine I §7。二重 loop の成分の幾何的な模型。 -/
def doubleCircleRestriction (Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHom CirclePower.space.{u}
      (PointedObject.basedHom CirclePower.space.{u} Y) ⟶
    PointedObject.basedHom PointedSimplicialSet.circle.{u}
      (PointedObject.basedHom PointedSimplicialSet.circle.{u} Y) :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X := PointedSimplicialSet.circle.{u}) (Y := CirclePower.space.{u})
    CirclePower.unit.{u} (PointedObject.basedHom CirclePower.space.{u} Y) ≫
    PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
      (Y := PointedObject.basedHom CirclePower.space.{u} Y)
      (Z := PointedObject.basedHom PointedSimplicialSet.circle.{u} Y)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Y)

/-- 概要：二つの円の制限は全基点の全次数でホモトピー類の同型を誘導する。
方針：anodyne な源の制限の全単射 RLP と、標的の π_* 同型の内部 Hom での保存を使う。
規約：標的 Y の Kan 性だけを仮定する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。Kan 円の変数交換を通常の円で判定する。 -/
theorem doubleCircleRestriction_piIsomorphism (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (doubleCircleRestriction Y).right := by
  have hinner : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit Y).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp CirclePower.unit
        (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle.{u}) Y)
  have houter : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit
        (PointedObject.basedHom CirclePower.space Y)).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp CirclePower.unit
        (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle.{u}) _)
  exact houter.comp (PointedMapping.post_piIsomorphism PointedSimplicialSet.circle _ hinner)

end

end SerrePositivity.KST.Spectra
