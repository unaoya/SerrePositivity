module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastCocone
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetClosureRetraction

/-!
概要：中央の八頂点添字を三点 span へ収縮し余極限性を制限する。
方針：同じ実図式の native 余錐と頂点を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の中央面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

def IsExcisionGridCenterSpan (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastIndex.{u}) : Prop :=
  1 ≤ p.val.val.val.down.val.1.val ∧ 1 ≤ p.val.val.val.down.val.2.val

def excisionGridPastRaise : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastIndex.{u} →o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastIndex.{u} where
  toFun p := by
    let x : Fin 3 := ⟨max p.val.val.val.down.val.1.val 1, by
      have := p.val.property.1; omega⟩
    let y : Fin 3 := ⟨max p.val.val.val.down.val.2.val 1, by
      have := p.val.property.2; omega⟩
    exact ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint x y, by
      have hp := p.property
      have hx := p.val.property.1
      have hy := p.val.property.2
      change p.val.val.val.down.val.1.val + p.val.val.val.down.val.2.val ≤ 3 at hp
      change max p.val.val.val.down.val.1.val 1 + max p.val.val.val.down.val.2.val 1 ≤ 3
      omega⟩
  monotone' := by
    intro a b h
    constructor
    · change max a.val.val.val.down.val.1.val 1 ≤ max b.val.val.val.down.val.1.val 1
      exact max_le_max h.1 le_rfl
    · change max a.val.val.val.down.val.2.val 1 ≤ max b.val.val.val.down.val.2.val 1
      exact max_le_max h.2 le_rfl

lemma excisionGridPastRaise_ge (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastIndex.{u}) :
    p ≤ excisionGridPastRaise p := ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩

lemma excisionGridPastRaise_mem (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastIndex.{u}) :
    IsExcisionGridCenterSpan (excisionGridPastRaise p) :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

lemma excisionGridPastRaise_fixed (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastIndex.{u})
    (hp : IsExcisionGridCenterSpan p) : excisionGridPastRaise p = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact max_eq_left hp.1
  · exact max_eq_left hp.2

lemma excisionGridCenterSpan_rightAnodyne : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastIndex.{u})
      (fun v ↦ IsExcisionGridCenterSpan (nerveEquiv v))).ι :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetClosure_rightAnodyne IsExcisionGridCenterSpan excisionGridPastRaise
    excisionGridPastRaise_ge excisionGridPastRaise_mem excisionGridPastRaise_fixed

lemma ExcisionGridExtension.center_span_colimit {X : SSet.{u}} [Quasicategory X]
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension G z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone d.core _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPastCocone).restrict
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastIndex.{u})
        (fun v ↦ IsExcisionGridCenterSpan (nerveEquiv v))).ι) :=
  d.past_cocone_colimit.restrict_of_rightAnodyne _ excisionGridCenterSpan_rightAnodyne

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
