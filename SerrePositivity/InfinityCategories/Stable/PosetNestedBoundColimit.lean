module
public import SerrePositivity.InfinityCategories.Stable.PosetNestedCanonicalRestriction
public import SerrePositivity.InfinityCategories.Stable.PosetNestedBoundCocone

/-!
概要：同じ上界への部分図式の実余錐に局所余極限を移す。
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

lemma isColimit_mapJoinCocone_of_poset_nested_canonical_bound
    (T U : P → Prop) (hTU : ∀ p, T p → U p) (c : P)
    (hbound : ∀ p, T p → p ≤ c)
    (d : JoinCocone (nerveMap (posetSubtypeInclusion U))) (hd : d.vertex = nerveVertex c)
    {X : SSet.{u}} [Quasicategory X] (F : nerve P ⟶ X)
    (hF : ∀ p : (nerve P) _⦋0⦌,
      IsColimitCone (leftKanCanonicalCocone (nerveMap (posetSubtypeInclusion T)) F p)) :
    IsColimitCone (mapJoinCocone F d) := by
  apply (isColimitCone_iff_restrict_of_poset_nested_canonical T U hTU F hF
    (mapJoinCocone F d)).mpr
  have hl := isColimit_posetSubtypeLowerCocone_of_canonical T c F (hF (nerveVertex c))
  have he := (isColimitCone_iff_restrict_of_isIso _
    (posetNestedBoundLowerNerveIso T U hTU c hbound).hom).mp hl
  apply (isColimitCone_iff_of_val_eq _ _ ?_).mpr he
  have hv := congrArg (fun f ↦ f ≫ F)
    (posetNestedBoundCocone_restrict_val T U hTU c hbound d hd)
  simpa only [mapJoinCocone, JoinCocone.restrict, Category.assoc] using hv

end SerrePositivity.InfinityCategories
