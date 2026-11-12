module

public import SerrePositivity.KST.LocalizingInvariants.DGStrictAdjointComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorClosedCycles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPostcompositionComponents

/-!
概要：厳密 dg 左随伴比較の成分を、元の閉零射の通常の随伴比較式へ同定する。
方針：閉零 cycle の合成と dg 関手の像を、D の元の閉射への作用と比較する。
規約：元の実成分を保持。使われ方：随伴一意性の自然同型の可逆性を実比較へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]

lemma dgClosedCycle_comp {x y z : ClosedCategory R E} (f : x ⟶ y) (g : y ⟶ z) :
    compose R (closedHomEquiv R E _ _ g).val (closedHomEquiv R E _ _ f).val (zero_add 0) =
      (closedHomEquiv R E _ _ (f ≫ g)).val := by
  have h := congrArg Subtype.val (closedHomEquiv_postcompose R E f g)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition_f R E g 0 (closedHomEquiv R E _ _ f).val).symm.trans h

variable {R E} {C : Type v} [DGCategory R C]
  (L L' : DGFunctor R C E) (Q : DGFunctor R E C)
  (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (DGFunctor.id C) (L'.comp Q))
  (ε : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (Q.comp L) (DGFunctor.id E)) (x : C)
  (a : ForgetEnrichment.of (Complex R) x ⟶
    ForgetEnrichment.of (Complex R) (Q.obj (L'.obj x)))
  (b : ForgetEnrichment.of (Complex R) (L.obj (Q.obj (L'.obj x))) ⟶
    ForgetEnrichment.of (Complex R) (L'.obj x))

lemma dgStrictAdjointComparison_app_eq
    (ha : η.app x = closedHomEquiv R C _ _ a)
    (hb : ε.app (L'.obj x) = closedHomEquiv R E _ _ b) :
    (dgStrictAdjointComparison L L' Q η ε).app x =
      closedHomEquiv R E _ _ (L.onClosed.map a ≫ b) := by
  apply Subtype.ext
  change compose R (ε.app (L'.obj x)).val
    ((L.map x (Q.obj (L'.obj x))).f 0 (η.app x).val) (zero_add 0) = _
  rw [ha, hb]
  have he : (L.map x (Q.obj (L'.obj x))).f 0 (closedHomEquiv R C _ _ a).val =
      (closedHomEquiv R E _ _ (L.onClosed.map a)).val := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle L a
  exact (congrArg (fun t => compose R (closedHomEquiv R E _ _ b).val t (zero_add 0)) he).trans
    (dgClosedCycle_comp R E (L.onClosed.map a) b)

end SerrePositivity.KST.LocalizingInvariants
