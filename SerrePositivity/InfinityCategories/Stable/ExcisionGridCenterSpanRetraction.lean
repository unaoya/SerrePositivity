module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridPastCocone
public import SerrePositivity.InfinityCategories.Stable.PosetClosureRetraction

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
namespace SerrePositivity.InfinityCategories
variable {P : Type u} [PartialOrder P]

def IsExcisionGridCenterSpan (p : ExcisionGridPastIndex.{u}) : Prop :=
  1 ≤ p.val.val.val.down.val.1.val ∧ 1 ≤ p.val.val.val.down.val.2.val

def excisionGridPastRaise : ExcisionGridPastIndex.{u} →o ExcisionGridPastIndex.{u} where
  toFun p := by
    let x : Fin 3 := ⟨max p.val.val.val.down.val.1.val 1, by
      have := p.val.property.1; omega⟩
    let y : Fin 3 := ⟨max p.val.val.val.down.val.2.val 1, by
      have := p.val.property.2; omega⟩
    exact ⟨excisionGridCorePoint x y, by
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

lemma excisionGridPastRaise_ge (p : ExcisionGridPastIndex.{u}) :
    p ≤ excisionGridPastRaise p := ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩

lemma excisionGridPastRaise_mem (p : ExcisionGridPastIndex.{u}) :
    IsExcisionGridCenterSpan (excisionGridPastRaise p) :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

lemma excisionGridPastRaise_fixed (p : ExcisionGridPastIndex.{u})
    (hp : IsExcisionGridCenterSpan p) : excisionGridPastRaise p = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact max_eq_left hp.1
  · exact max_eq_left hp.2

lemma excisionGridCenterSpan_rightAnodyne : rightAnodyneExtensions
    (fullSubcomplexOnVertices (nerve ExcisionGridPastIndex.{u})
      (fun v ↦ IsExcisionGridCenterSpan (nerveEquiv v))).ι :=
  posetClosure_rightAnodyne IsExcisionGridCenterSpan excisionGridPastRaise
    excisionGridPastRaise_ge excisionGridPastRaise_mem excisionGridPastRaise_fixed

lemma ExcisionGridExtension.center_span_colimit {X : SSet.{u}} [Quasicategory X]
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    IsColimitCone ((mapJoinCocone d.core excisionGridPastCocone).restrict
      (fullSubcomplexOnVertices (nerve ExcisionGridPastIndex.{u})
        (fun v ↦ IsExcisionGridCenterSpan (nerveEquiv v))).ι) :=
  d.past_cocone_colimit.restrict_of_rightAnodyne _ excisionGridCenterSpan_rightAnodyne

end SerrePositivity.InfinityCategories
