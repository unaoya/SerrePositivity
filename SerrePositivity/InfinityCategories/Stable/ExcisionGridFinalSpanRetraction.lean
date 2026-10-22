module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridFullPastCocone
public import SerrePositivity.InfinityCategories.Stable.PosetClosureRetraction

/-!
概要：十三頂点の実添字を三点 span へ固定収縮する。
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
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def IsExcisionGridFinalSpan (p : ExcisionGridFullPastIndex.{u}) : Prop :=
  2 ≤ p.val.down.val.1.val ∧ 2 ≤ p.val.down.val.2.val

def excisionGridFullPastRaise :
    ExcisionGridFullPastIndex.{u} →o ExcisionGridFullPastIndex.{u} where
  toFun p := by
    let x : Fin 4 := ⟨max p.val.down.val.1.val 2, by
      have := p.val.down.val.1.isLt; omega⟩
    let y : Fin 4 := ⟨max p.val.down.val.2.val 2, by
      have := p.val.down.val.2.isLt; omega⟩
    let q : ExcisionGridIndex.{u} := ULift.up ⟨(x, y), by
      have hx := p.val.down.val.1.isLt
      have hy := p.val.down.val.2.isLt
      dsimp [x, y]
      omega⟩
    exact ⟨q, by
      have hp := p.property
      have hx := p.val.down.val.1.isLt
      have hy := p.val.down.val.2.isLt
      change p.val.down.val.1.val + p.val.down.val.2.val ≤ 5 at hp
      change max p.val.down.val.1.val 2 + max p.val.down.val.2.val 2 ≤ 5
      omega⟩
  monotone' := by
    intro a b h
    constructor
    · change max a.val.down.val.1.val 2 ≤ max b.val.down.val.1.val 2
      exact max_le_max h.1 le_rfl
    · change max a.val.down.val.2.val 2 ≤ max b.val.down.val.2.val 2
      exact max_le_max h.2 le_rfl

lemma excisionGridFullPastRaise_ge (p : ExcisionGridFullPastIndex.{u}) :
    p ≤ excisionGridFullPastRaise p := ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩

lemma excisionGridFullPastRaise_mem (p : ExcisionGridFullPastIndex.{u}) :
    IsExcisionGridFinalSpan (excisionGridFullPastRaise p) :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

lemma excisionGridFullPastRaise_fixed (p : ExcisionGridFullPastIndex.{u})
    (hp : IsExcisionGridFinalSpan p) : excisionGridFullPastRaise p = p := by
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact max_eq_left hp.1
  · exact max_eq_left hp.2

lemma excisionGridFinalSpan_rightAnodyne : rightAnodyneExtensions
    (fullSubcomplexOnVertices (nerve ExcisionGridFullPastIndex.{u})
      (fun v ↦ IsExcisionGridFinalSpan (nerveEquiv v))).ι :=
  posetClosure_rightAnodyne IsExcisionGridFinalSpan excisionGridFullPastRaise
    excisionGridFullPastRaise_ge excisionGridFullPastRaise_mem excisionGridFullPastRaise_fixed

lemma ExcisionGridExtension.final_span_colimit {X : SSet.{u}} [Quasicategory X]
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    IsColimitCone ((mapJoinCocone d.full excisionGridFullPastCocone).restrict
      (fullSubcomplexOnVertices (nerve ExcisionGridFullPastIndex.{u})
        (fun v ↦ IsExcisionGridFinalSpan (nerveEquiv v))).ι) :=
  d.full_past_cocone_colimit.restrict_of_rightAnodyne _ excisionGridFinalSpan_rightAnodyne

end SerrePositivity.InfinityCategories
