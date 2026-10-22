module
public import SerrePositivity.InfinityCategories.Stable.PosetOrderIsoLowerCocone

/-!
概要：順序同型に沿って native 左 Kan の局所余極限を移す。
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

lemma posetSubtype_canonicalColimit_orderIso (e : P ≃o Q) (T : Q → Prop) (c : P)
    {X : SSet.{u}} (F : nerve Q ⟶ X)
    (h : IsColimitCone (leftKanCanonicalCocone (nerveMap (posetSubtypeInclusion T))
      F (nerveVertex (e c)))) :
    IsColimitCone (leftKanCanonicalCocone
      (nerveMap (posetSubtypeInclusion (fun p ↦ T (e p))))
      (nerveMap (posetOrderIsoFunctor e) ≫ F) (nerveVertex c)) := by
  have hl := isColimit_posetSubtypeLowerCocone_of_canonical T (e c) F h
  have he := (isColimitCone_iff_restrict_of_isIso _ (posetOrderIsoLowerNerveIso e T c).hom).mp hl
  have hn : IsColimitCone (mapJoinCocone (nerveMap (posetOrderIsoFunctor e) ≫ F)
      (posetSubtypeLowerCocone (fun p ↦ T (e p)) c)) := by
    apply (isColimitCone_iff_of_val_eq _ _ ?_).mpr he
    change (posetSubtypeLowerCocone (fun p ↦ T (e p)) c).val ≫
        (nerveMap (posetOrderIsoFunctor e) ≫ F) =
      ((posetSubtypeLowerCocone T (e c)).restrict (posetOrderIsoLowerNerveIso e T c).hom).val ≫ F
    rw [← Category.assoc, posetOrderIsoLowerCocone_val e T c]
  have hd := (isColimitCone_iff_of_val_eq _ _
    (posetSubtypeLowerCocone_postcomp_val (fun p ↦ T (e p)) c
      (nerveMap (posetOrderIsoFunctor e) ≫ F))).mp hn
  exact (isColimitCone_iff_restrict_of_isIso _
    (posetSubtypeLowerKanShapeIso (fun p ↦ T (e p)) c).hom).mpr hd

end SerrePositivity.InfinityCategories
