module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCenterPushout

/-!
概要：(3,2) の十頂点の実下方添字を三点 span へ固定収縮する。
方針：同じ実図式の native 余錐・頂点・二辺を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の外側の面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

abbrev excisionGridPoint32 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} := ULift.up ⟨(3, 2), by decide⟩

abbrev ExcisionGridRightLowerIndex :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle excisionGridPoint32.{u}

def IsExcisionGridRightSpan (p : ExcisionGridRightLowerIndex.{u}) : Prop :=
  2 ≤ p.val.down.val.1.val ∧ 1 ≤ p.val.down.val.2.val

def excisionGridRightLowerRaise :
    ExcisionGridRightLowerIndex.{u} →o ExcisionGridRightLowerIndex.{u} where
  toFun p := by
    let x : Fin 4 := ⟨max p.val.down.val.1.val 2, by
      have := p.val.down.val.1.isLt; omega⟩
    let y : Fin 4 := ⟨max p.val.down.val.2.val 1, by
      have := p.property.2.2
      change p.val.down.val.2.val ≤ 2 at this
      omega⟩
    let q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} := ULift.up ⟨(x, y), by
      have hy := p.property.2.2
      change p.val.down.val.2.val ≤ 2 at hy
      have hx := p.val.down.val.1.isLt
      dsimp [x, y]
      omega⟩
    have hq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle q := by
      have hp := p.property.1
      have hy := p.property.2.2
      change p.val.down.val.2.val ≤ 2 at hy
      dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCore] at hp
      dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCore, q, x, y]
      omega
    exact ⟨q, hq, by
      constructor
      · change max p.val.down.val.1.val 2 ≤ 3
        have := p.val.down.val.1.isLt; omega
      · change max p.val.down.val.2.val 1 ≤ 2
        have := p.property.2.2
        change p.val.down.val.2.val ≤ 2 at this
        omega⟩
  monotone' := by
    intro a b h
    constructor
    · change max a.val.down.val.1.val 2 ≤ max b.val.down.val.1.val 2
      exact max_le_max h.1 le_rfl
    · change max a.val.down.val.2.val 1 ≤ max b.val.down.val.2.val 1
      exact max_le_max h.2 le_rfl

lemma excisionGridRightLowerRaise_ge (p : ExcisionGridRightLowerIndex.{u}) :
    p ≤ excisionGridRightLowerRaise p := ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩

lemma excisionGridRightLowerRaise_mem (p : ExcisionGridRightLowerIndex.{u}) :
    IsExcisionGridRightSpan (excisionGridRightLowerRaise p) :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

lemma excisionGridRightLowerRaise_fixed (p : ExcisionGridRightLowerIndex.{u})
    (hp : IsExcisionGridRightSpan p) : excisionGridRightLowerRaise p = p := by
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact max_eq_left hp.1
  · exact max_eq_left hp.2

lemma excisionGridRightSpan_rightAnodyne : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve ExcisionGridRightLowerIndex.{u})
      (fun v ↦ IsExcisionGridRightSpan (nerveEquiv v))).ι :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetClosure_rightAnodyne IsExcisionGridRightSpan excisionGridRightLowerRaise
    excisionGridRightLowerRaise_ge excisionGridRightLowerRaise_mem
    excisionGridRightLowerRaise_fixed

lemma ExcisionGridExtension.right_span_colimit {X : SSet.{u}} [Quasicategory X]
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension G z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone d.full
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle excisionGridPoint32)).restrict
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve ExcisionGridRightLowerIndex.{u})
        (fun v ↦ IsExcisionGridRightSpan (nerveEquiv v))).ι) :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isColimit_posetSubtypeLowerCocone_of_canonical _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle excisionGridPoint32
    d.full (d.full_colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex excisionGridPoint32))).restrict_of_rightAnodyne _
      excisionGridRightSpan_rightAnodyne

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
