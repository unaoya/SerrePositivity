module

public import SerrePositivity.KST.Spectra.CircleReversalHomotopy
public import SerrePositivity.KST.Spectra.PointedIhomIntervalNaturality

/-!
概要：二重 loop の二重符号反転を、円自身の一つの区間から自然に構成する。
方針：同じ前合成区間へ内部 Hom を作用させ、前合成・後合成の厳密交換を使う。
規約：標的ごとの充填選択を除く。使われ方：構造比較の自然な符号打ち消し辺。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.CirclePower

/-- 元の内側の円の符号反転を、二重 loop の射として明示する。 -/
def nestedReversal (Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHom space.{u} (PointedObject.basedHom space.{u} Y) ⟶
      PointedObject.basedHom space.{u} (PointedObject.basedHom space.{u} Y) :=
  PointedObject.basedHomMap space.{u}
    (Y := PointedObject.basedHom space.{u} Y) (Z := PointedObject.basedHom space.{u} Y)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (integerPowerMap.{u} (-1)) Y)

/-- 二重 loop の内側の符号を二度反転する区間も、円自身の同じ区間から得る。 -/
def nestedReversalTwicePath (Y : PointedSimplicialSet.{u}) :
    PointedMapping.VerticalPath (PointedObject.toPoint
      (PointedObject.basedHom space.{u} (PointedObject.basedHom space.{u} Y)))
      (nestedReversal Y ≫ nestedReversal Y)
      (𝟙 (PointedObject.basedHom space.{u} (PointedObject.basedHom space.{u} Y))) := by
  have hs : nestedReversal Y ≫ nestedReversal Y =
      (ihom space.{u}).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (integerPowerMap.{u} (-1)) Y ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (integerPowerMap.{u} (-1)) Y) := by
    exact (CategoryTheory.Functor.map_comp (ihom space.{u})
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (integerPowerMap.{u} (-1)) Y)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (integerPowerMap.{u} (-1)) Y)).symm
  have ht : 𝟙 (PointedObject.basedHom space.{u} (PointedObject.basedHom space.{u} Y)) =
      (ihom space.{u}).map (𝟙 (PointedObject.basedHom space.{u} Y)) :=
    (CategoryTheory.Functor.map_id (ihom space.{u}) (PointedObject.basedHom space.{u} Y)).symm
  exact ((reversalTwicePre Y).basedIhomMap space.{u}).changeEndpoints hs ht

/-- この区間の実辺も、円自身の区間への同じ内部 Hom の作用。 -/
lemma nestedReversalTwicePath_path (Y : PointedSimplicialSet.{u}) :
    (nestedReversalTwicePath Y).path = ((reversalTwicePre Y).basedIhomMap space.{u}).path := rfl

/-- 二重 loop の二重反転区間は、任意の標的射への後合成と辺全体で自然。 -/
lemma nestedReversalTwicePath_natural {Y Z : PointedSimplicialSet.{u}} (v : Y ⟶ Z) :
    ((nestedReversalTwicePath Y).basedPost (PointedObject.basedHomMap space.{u}
      (Y := PointedObject.basedHom space.{u} Y) (Z := PointedObject.basedHom space.{u} Z)
      (PointedObject.basedHomMap space.{u} (Y := Y) (Z := Z) v))).path =
    ((nestedReversalTwicePath Z).pre (PointedObject.basedHomMap space.{u}
      (Y := PointedObject.basedHom space.{u} Y) (Z := PointedObject.basedHom space.{u} Z)
      (PointedObject.basedHomMap space.{u} (Y := Y) (Z := Z) v))).path := by
  let q := PointedObject.basedHomMap space.{u} (Y := Y) (Z := Z) v
  change (nestedReversalTwicePath Y).path ≫ _ = (nestedReversalTwicePath Z).path ≫ _
  rw [nestedReversalTwicePath_path, nestedReversalTwicePath_path]
  have h := reversalTwicePre_natural v
  have ht := congrArg (· ≫ (PointedMapping.ihomAction space.{u}
    (PointedObject.basedHom space.{u} Y) (PointedObject.basedHom space.{u} Z)).right) h
  change (((reversalTwicePre Y).basedPost q).basedIhomMap space.{u}).path =
    (((reversalTwicePre Z).pre q).basedIhomMap space.{u}).path at ht
  exact ((reversalTwicePre Y).basedIhomMap_post_path space.{u} q).symm.trans
    (ht.trans ((reversalTwicePre Z).basedIhomMap_pre_path_natural space.{u} q))

end SerrePositivity.KST.Spectra.CirclePower
