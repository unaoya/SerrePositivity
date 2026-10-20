module

public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalMappingOppositeComposition
public import SerrePositivity.InfinityCategories.F1B.KanParameterizedFullFaithfulness

/-!
概要：区間写像空間の反転と元の関手の後合成を照合する。
方針：標準 Hom の式と、相対境界充填の判定を使用する。
規約：元の対象・射・端点の同一視を保持する。使われ方：一般 coherent 極限保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 区間族の反転は、元の関手の後合成と可換である。 -/
lemma intervalReverseFamily_postcomp {A X Y : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) (G : X ⟶ Y) :
    intervalReverseFamily (f ≫ intervalFunctorMap G x y) =
      intervalReverseFamily f ≫ intervalFunctorMap (SSet.opFunctor.map G)
        (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) := by
  apply intervalMappingUncurry_injective
  rw [intervalReverseFamily_uncurry, intervalFunctorMap_uncurry, reversePrism_postcomp,
    intervalFunctorMap_uncurry, intervalReverseFamily_uncurry]

/-- 区間写像空間の反対同型は、元の関手に自然である。 -/
lemma intervalOppositeIso_naturality {X Y : SSet.{u}} (G : X ⟶ Y) (x y : X _⦋0⦌) :
    SSet.opFunctor.map (intervalFunctorMap G x y) ≫
        (intervalOppositeIso (G.app (Opposite.op ⦋0⦌) x) (G.app (Opposite.op ⦋0⦌) y)).hom =
      (intervalOppositeIso x y).hom ≫ intervalFunctorMap (SSet.opFunctor.map G)
        (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) := by
  rw [← intervalReverseFamily_eq (X := Y) (G.app (Opposite.op ⦋0⦌) x)
    (G.app (Opposite.op ⦋0⦌) y) (intervalFunctorMap G x y)]
  change intervalReverseFamily (intervalFunctorMap G x y) =
    intervalReverseFamily (𝟙 (intervalMappingSpace x y)) ≫
      intervalFunctorMap (X := X.op) (Y := Y.op) (SSet.opFunctor.map G)
        (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)
  simpa only [Category.id_comp] using
    intervalReverseFamily_postcomp (𝟙 (intervalMappingSpace x y)) G

/-- 元の区間写像空間比較の同値性は反対の比較へ移る。 -/
lemma intervalFunctorMap_op_isQCatEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (x y : X _⦋0⦌)
    (h : IsQCatEquivalence (intervalFunctorMap f x y)) :
    IsQCatEquivalence (intervalFunctorMap (SSet.opFunctor.map f)
      (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)) := by
  have hop := F1B.kanIsQCatEquivalence_op h
  have hs := (qCatEquivalenceOfIso (intervalOppositeIso x y)).isQCatEquivalence
  have ht := (qCatEquivalenceOfIso (intervalOppositeIso
    (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y))).isQCatEquivalence
  have hc := hop.comp ht
  change IsQCatEquivalence (SSet.opFunctor.map (intervalFunctorMap f x y) ≫
    (intervalOppositeIso (f.app (Opposite.op ⦋0⦌) x)
      (f.app (Opposite.op ⦋0⦌) y)).hom) at hc
  rw [intervalOppositeIso_naturality f x y] at hc
  exact hs.cancel_left hc

/-- 元の区間写像空間比較の同値性を pinched Hom 比較へ移す。 -/
lemma pinchedHomMap_equivalence_of_intervalFunctorMap {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (x y : X _⦋0⦌)
    (h : IsQCatEquivalence (intervalFunctorMap f x y)) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap f x y) := by
  have hc := (PinchedInterval.comparison_isQCatEquivalence x y).comp h
  rw [← pinchedIntervalComparison_naturality] at hc
  have hh := (PinchedInterval.comparison_isQCatEquivalence
    (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)).cancel_right hc
  exact hh.isSimplicialHomotopyEquivalence

end
end SerrePositivity.InfinityCategories.HomotopyLimits
