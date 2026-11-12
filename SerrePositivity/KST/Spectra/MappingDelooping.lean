module

public import SerrePositivity.KST.Spectra.KanLoopLift
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism

/-!
概要：Ω 条件を任意の源を持つ写像空間へ移す。
方針：Kan 円への持ち上げの後合成と内部 Hom の源の交換を合成する。
規約：源 A の Kan 性は要求しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。パラメータを内側へ移した標的の Ω 条件。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：通常の Ω 条件の射から写像空間の Kan 円への delooping 射を作る。
方針：Kan 円へ持ち上げて後合成し、パラメータ源と円を交換する。
規約：点つき写像空間の実際の射。
使われ方：BF 1978 §2、HA §1.4.2。任意のパラメータで交換の符号を計算する。 -/
def mappingKanDelooping (A : PointedSimplicialSet.{u})
    {Y Z : PointedSimplicialSet.{u}} [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z) :
    PointedObject.basedHom A Y ⟶
      PointedObject.basedHom CirclePower.space.{u} (PointedObject.basedHom A Z) :=
  PointedObject.basedHomMap A (kanLoopLift a) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A CirclePower.space.{u} Z).hom

/-- 概要：写像空間への delooping 射は元の Ω 条件が同型なら全基点 π_* 同型。
方針：標的の同型の後合成での保存と源の交換の厳密な同型を合成する。
規約：元の Ω 条件は零次数を含む全基点で仮定する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。写像空間の標的での交換の符号の適用条件。 -/
theorem mappingKanDelooping_piIsomorphism (A : PointedSimplicialSet.{u})
    {Y Z : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (mappingKanDelooping A a).right := by
  have hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (PointedObject.basedHomMap A (kanLoopLift a)).right :=
    PointedMapping.post_piIsomorphism A (kanLoopLift a) (kanLoopLift_piIsomorphism a ha)
  let e := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A CirclePower.space.{u} Z
  have : KanComplex ((ihom A).obj ((ihom CirclePower.space.{u}).obj Z)).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex A (PointedObject.basedHom CirclePower.space Z)
  have : KanComplex ((ihom CirclePower.space.{u}).obj ((ihom A).obj Z)).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex CirclePower.space (PointedObject.basedHom A Z)
  let e' : (PointedObject.basedHom A (PointedObject.basedHom CirclePower.space.{u} Z)).right ≅
      (PointedObject.basedHom CirclePower.space.{u} (PointedObject.basedHom A Z)).right :=
    PointedSimplicialSet.forget.mapIso e
  have he : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism e.hom.right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e'
  exact hp.comp he

end

end SerrePositivity.KST.Spectra
