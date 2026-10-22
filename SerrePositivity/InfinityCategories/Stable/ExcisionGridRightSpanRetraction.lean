module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCenterPushout

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
namespace SerrePositivity.InfinityCategories

abbrev excisionGridPoint32 : ExcisionGridIndex.{u} := ULift.up ⟨(3, 2), by decide⟩

abbrev ExcisionGridRightLowerIndex :=
  PosetSubtypeLowerIndex IsExcisionGridMiddle excisionGridPoint32.{u}

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
    let q : ExcisionGridIndex.{u} := ULift.up ⟨(x, y), by
      have hy := p.property.2.2
      change p.val.down.val.2.val ≤ 2 at hy
      have hx := p.val.down.val.1.isLt
      dsimp [x, y]
      omega⟩
    have hq : IsExcisionGridMiddle q := by
      have hp := p.property.1
      have hy := p.property.2.2
      change p.val.down.val.2.val ≤ 2 at hy
      dsimp only [IsExcisionGridMiddle, IsExcisionGridCore] at hp
      dsimp only [IsExcisionGridMiddle, IsExcisionGridCore, q, x, y]
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

lemma excisionGridRightSpan_rightAnodyne : rightAnodyneExtensions
    (fullSubcomplexOnVertices (nerve ExcisionGridRightLowerIndex.{u})
      (fun v ↦ IsExcisionGridRightSpan (nerveEquiv v))).ι :=
  posetClosure_rightAnodyne IsExcisionGridRightSpan excisionGridRightLowerRaise
    excisionGridRightLowerRaise_ge excisionGridRightLowerRaise_mem
    excisionGridRightLowerRaise_fixed

lemma ExcisionGridExtension.right_span_colimit {X : SSet.{u}} [Quasicategory X]
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    IsColimitCone ((mapJoinCocone d.full
      (posetSubtypeLowerCocone IsExcisionGridMiddle excisionGridPoint32)).restrict
      (fullSubcomplexOnVertices (nerve ExcisionGridRightLowerIndex.{u})
        (fun v ↦ IsExcisionGridRightSpan (nerveEquiv v))).ι) :=
  (isColimit_posetSubtypeLowerCocone_of_canonical IsExcisionGridMiddle excisionGridPoint32
    d.full (d.full_colimit (nerveVertex excisionGridPoint32))).restrict_of_rightAnodyne _
      excisionGridRightSpan_rightAnodyne

end SerrePositivity.InfinityCategories
