module

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource
public import SerrePositivity.KST.Spectra.PositiveLoopNaturality
public import SerrePositivity.KST.Spectra.SphereMappingHomotopyFormula

/-!
概要：loop 値の写像空間の正次数群を元の写像空間の一つ高い次数へ移す。
方針：二つの源の交換同型と loop の群同型を合成し、源の射への自然性を証明する。
規約：通常の円を用いる。球面の次数移動の帰納段と同じ向き。
使われ方：Goerss–Jardine I §7、VIII §1。骨格 fiber の係数比較の高次数への反復。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：任意の源からの写像空間と通常の loop の順序を交換する。
方針：内部 Hom の二つの源を交換する。
規約：係数の Kan 性はこの厳密な同型には不要。
使われ方：Goerss–Jardine I §7。写像空間の高次数の比較。 -/
def loopSwap (A Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedObject.basedHom A Y) ≅ PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u} A Y

@[reassoc]
lemma loopSwap_pre {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
        (Y := PointedObject.basedHom B Y) (Z := PointedObject.basedHom A Y)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y) ≫ (loopSwap A Y).hom =
      (loopSwap B Y).hom ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right (C := PointedSimplicialSet.{u})
    PointedSimplicialSet.circle.{u} i Y
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  change PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
      (Y := PointedObject.basedHom B Y) (Z := PointedObject.basedHom A Y)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y) ≫ (loopSwap A Y).hom =
    (loopSwap B Y).hom ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) at h
  exact h

/-- 概要：loop 値の写像空間の π_(r+1) を元の写像空間の π_(r+2) へ移す。
方針：交換同型の逆射と通常の loop の群同型を合成する。
規約：全ての正次数で群同型。
使われ方：Goerss–Jardine I §7、VIII §1。係数の次数移動の反復。 -/
def loopPositiveEquiv (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right r
        (PointedSimplicialSet.basepoint (PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y))) ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom A Y).right (r + 1)
        (PointedSimplicialSet.basepoint (PointedObject.basedHom A Y)) := by
  let e : (PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right ≅
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedObject.basedHom A Y)).right :=
    PointedSimplicialSet.forget.mapIso (loopSwap A Y).symm
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso r e
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (loopSwap A Y).inv)).trans
      (loopPositiveHomotopyEquiv (PointedObject.basedHom A Y) r)

lemma loopPositiveEquiv_apply (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (r : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right r
      (PointedSimplicialSet.basepoint (PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)))) :
    loopPositiveEquiv A Y r a = loopPositiveHomotopyEquiv (PointedObject.basedHom A Y) r
      (pointedGroupMap r (loopSwap A Y).inv a) := rfl

/-- 概要：loop 値の正次数比較は源の射による制限と可換。
方針：交換同型の逆射の可換式を群へ送り、通常の loop の自然性を適用する。
規約：源の射は任意。単射性を要求しない。
使われ方：Goerss–Jardine VIII §1。セル球面への制限と高次数比較の交換。 -/
theorem loopPositiveEquiv_pre {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom B (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right r
      (PointedSimplicialSet.basepoint (PointedObject.basedHom B (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)))) :
    loopPositiveEquiv A Y r (pointedGroupMap r (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) a) =
      pointedGroupMap (r + 1) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y) (loopPositiveEquiv B Y r a) := by
  have hs := congrArg (fun t ↦ (loopSwap B Y).inv ≫ t ≫ (loopSwap A Y).inv)
    (loopSwap_pre i Y)
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] at hs
  have hg := congrArg (fun f : PointedObject.basedHom B (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedObject.basedHom A Y) ↦
      pointedGroupMap r f a) hs
  simp only [pointedGroupMap_comp] at hg
  rw [loopPositiveEquiv_apply, loopPositiveEquiv_apply, ← hg]
  exact loopPositiveHomotopyEquiv_natural (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y) r _

end
end SerrePositivity.KST.Spectra.PointedMapping
