module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStrictNatTransWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGStrictNatTransAlgebra

/-!
概要：元の厳密 dg 単位・余単位から、左随伴比較の全 Hom 自然性を構成する。
方針：通常の随伴一意性と同じ成分を使い、二つの厳密自然性と結合律で比較する。
規約：三角式や比較の可逆性を新たな入力に隠さない。使われ方：実延長の合成同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {C E : Type v} [DGCategory R C] [DGCategory R E]
  (L L' : DGFunctor R C E) (Q : DGFunctor R E C)
  (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (DGFunctor.id C) (L'.comp Q))
  (ε : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (Q.comp L) (DGFunctor.id E))

/-- 元の単位を L で写した後に元の余単位を適用する、全斉次射に自然な比較。 -/
def dgStrictAdjointComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans L L' where
  app x := by
    let a : zeroCycles (homObject R E (L.obj x) (L.obj (Q.obj (L'.obj x)))) :=
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η L).app x
    let b : zeroCycles (homObject R E (L.obj (Q.obj (L'.obj x))) (L'.obj x)) :=
      ε.app (L'.obj x)
    refine ⟨compose R b.val a.val (zero_add 0), ?_⟩
    change differential R (compose R b.val a.val (zero_add 0)) = 0
    have ha : differential R a.val = 0 := a.property
    have hb : differential R b.val = 0 := b.property
    rw [differential_compose, ha, hb]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, zero_add]
  naturality {x y k} f := by
    let u := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η L
    have hu := u.naturality f
    change compose R (u.app y).val ((L.map x y).f k f) (add_zero k) =
      compose R ((L.map _ _).f k ((Q.map _ _).f k ((L'.map x y).f k f)))
        (u.app x).val (zero_add k) at hu
    have he := ε.naturality ((L'.map x y).f k f)
    change compose R (ε.app (L'.obj y)).val
        ((L.map _ _).f k ((Q.map _ _).f k ((L'.map x y).f k f))) (add_zero k) =
      compose R ((L'.map x y).f k f) (ε.app (L'.obj x)).val (zero_add k) at he
    change compose R (compose R (ε.app (L'.obj y)).val (u.app y).val (zero_add 0))
        ((L.map x y).f k f) (add_zero k) =
      compose R ((L'.map x y).f k f)
        (compose R (ε.app (L'.obj x)).val (u.app x).val (zero_add 0)) (zero_add k)
    calc
      _ = compose R (ε.app (L'.obj y)).val
          (compose R (u.app y).val ((L.map x y).f k f) (add_zero k)) (add_zero k) :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ (add_zero k) (zero_add 0) (add_zero k)).symm
      _ = compose R (ε.app (L'.obj y)).val
          (compose R ((L.map _ _).f k ((Q.map _ _).f k ((L'.map x y).f k f)))
            (u.app x).val (zero_add k)) (add_zero k) := by rw [hu]
      _ = compose R (compose R (ε.app (L'.obj y)).val
          ((L.map _ _).f k ((Q.map _ _).f k ((L'.map x y).f k f))) (add_zero k))
            (u.app x).val (zero_add k) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ (zero_add k) (add_zero k) (add_zero k)
      _ = compose R (compose R ((L'.map x y).f k f)
          (ε.app (L'.obj x)).val (zero_add k)) (u.app x).val (zero_add k) := by rw [he]
      _ = _ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ (zero_add 0) (zero_add k) (zero_add k)).symm

end SerrePositivity.KST.LocalizingInvariants
