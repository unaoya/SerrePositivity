module
public import SerrePositivity.InfinityCategories.Stable.PosetNestedLowerCocone
public import SerrePositivity.InfinityCategories.F1.Ind.InitialBoundaryCoconeRestriction
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCanonicalMapping

/-!
概要：同じ左 Kan の局所余極限を部分図式へ移し native 余錐の制限を判定する。
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

lemma posetSubtype_canonicalColimit_nested (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : {p : P // U p}) {X : SSet.{u}} (F : nerve P ⟶ X)
    (h : IsColimitCone (leftKanCanonicalCocone (nerveMap (posetSubtypeInclusion T))
      F (nerveVertex c.val))) :
    IsColimitCone (leftKanCanonicalCocone
      (nerveMap (posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val)))
      (nerveMap (posetSubtypeInclusion U) ≫ F) (nerveVertex c)) := by
  have hl := isColimit_posetSubtypeLowerCocone_of_canonical T c.val F h
  have he := (isColimitCone_iff_restrict_of_isIso _
    (posetNestedLowerNerveIso T U hTU c).hom).mp hl
  have hn : IsColimitCone (mapJoinCocone (nerveMap (posetSubtypeInclusion U) ≫ F)
      (posetSubtypeLowerCocone (fun p : {p : P // U p} ↦ T p.val) c)) := by
    apply (isColimitCone_iff_of_val_eq _ _ ?_).mpr he
    change (posetSubtypeLowerCocone (fun p : {p : P // U p} ↦ T p.val) c).val ≫
        (nerveMap (posetSubtypeInclusion U) ≫ F) =
      ((posetSubtypeLowerCocone T c.val).restrict
        (posetNestedLowerNerveIso T U hTU c).hom).val ≫ F
    rw [← Category.assoc, posetNestedLowerCocone_val T U hTU c]
  have hd := (isColimitCone_iff_of_val_eq _ _
    (posetSubtypeLowerCocone_postcomp_val (fun p : {p : P // U p} ↦ T p.val) c
      (nerveMap (posetSubtypeInclusion U) ≫ F))).mp hn
  exact (isColimitCone_iff_restrict_of_isIso _
    (posetSubtypeLowerKanShapeIso (fun p : {p : P // U p} ↦ T p.val) c).hom).mpr hd

lemma isColimitCone_iff_restrict_of_poset_nested_canonical
    (T U : P → Prop) (hTU : ∀ p, T p → U p) {X : SSet.{u}} [Quasicategory X]
    (F : nerve P ⟶ X)
    (hF : ∀ p : (nerve P) _⦋0⦌,
      IsColimitCone (leftKanCanonicalCocone (nerveMap (posetSubtypeInclusion T)) F p))
    (d : JoinCocone (nerveMap (posetSubtypeInclusion U) ≫ F)) :
    IsColimitCone d ↔ IsColimitCone (d.restrict
      (nerveMap (posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val)))) := by
  let i := nerveMap (posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val))
  let : Mono i := posetSubtypeInclusion_nerveMap_mono _
  apply F2.Ind.isColimitCone_iff_restrict_of_initialBoundary i
  apply F1B.kanLeftCanonical_pre_initialBoundary
  intro c
  obtain ⟨c, rfl⟩ := nerveEquiv.symm.surjective c
  exact posetSubtype_canonicalColimit_nested T U hTU c F (hF (nerveVertex c.val))

end SerrePositivity.InfinityCategories
