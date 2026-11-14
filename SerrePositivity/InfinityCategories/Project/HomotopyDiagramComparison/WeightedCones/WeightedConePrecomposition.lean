module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSimplex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveTensor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFunctor

/-!
概要：weighted cone の初点を豊穣 Hom 全体の前合成で動かす。
方針：係数図式の豊穣合成と weighted nerve のパラメータ作用を組み合わせる。
規約：初点を動かすパラメータも単体順序を反転する。通常の射に制限しない。
使われ方：HTT 4.2.4.1 の cone simplex の合成と end の後合成の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 反転した二つの simplex の対の合成を戻すと、元の二つの simplex の対の合成になる。 -/
lemma reflectedSimplexMap_pair_comp {A B D : SSet.{u}} {n : ℕ}
    (a : Δ[n] ⟶ A.op) (b : Δ[n] ⟶ B.op) (c : A ⊗ B ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (lift a b ≫ (Functor.Monoidal.μIso SSet.opFunctor A B).hom ≫
        SSet.opFunctor.map c) =
      lift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap a) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap b) ≫ c := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap_post]
  rfl

/-- 豊穣 Hom の前合成は図式の各対象への後合成と可換。 -/
def simplicialHomPrecompositionDiagram (F : I ⥤ C) (x z : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ tensorRight (SimplicialCategory.sHom x z) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x where
  app i := (β_ (SimplicialCategory.sHom z (F.obj i))
    (SimplicialCategory.sHom x z)).hom ≫ eComp SSet x z (F.obj i)
  naturality i j f := by
    change (eHomWhiskerLeft SSet z (F.map f) ▷ SimplicialCategory.sHom x z) ≫
        (β_ (SimplicialCategory.sHom z (F.obj j)) (SimplicialCategory.sHom x z)).hom ≫
          eComp SSet x z (F.obj j) =
      ((β_ (SimplicialCategory.sHom z (F.obj i)) (SimplicialCategory.sHom x z)).hom ≫
        eComp SSet x z (F.obj i)) ≫ eHomWhiskerLeft SSet x (F.map f)
    rw [BraidedCategory.braiding_naturality_left_assoc, ← eComp_eHomWhiskerLeft, Category.assoc]

/-- 反転した係数図式での Hom(x,z).op 全体の前合成。 -/
def reflectedHomPrecompositionDiagram (F : I ⥤ C) (x z : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor) ⋙
        tensorRight (SimplicialCategory.sHom x z).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor :=
  (show (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor) ⋙
        tensorRight (SimplicialCategory.sHom x z).op ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ tensorRight (SimplicialCategory.sHom x z)) ⋙
        SSet.opFunctor from
    { app := fun i ↦ (Functor.Monoidal.μIso SSet.opFunctor
        (SimplicialCategory.sHom z (F.obj i)) (SimplicialCategory.sHom x z)).hom
      naturality := fun _ _ _ ↦ by rfl }) ≫
    Functor.whiskerRight (simplicialHomPrecompositionDiagram F x z) SSet.opFunctor

/-- weighted nerve の係数に反転した豊穣 Hom の全パラメータを前合成する射。 -/
def weightedConePrecompositionMap (F : I ⥤ C) (x z : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor) ⊗
        (SimplicialCategory.sHom x z).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor)
    (SimplicialCategory.sHom x z).op ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (reflectedHomPrecompositionDiagram F x z)

/-- 全 Hom パラメータによる前合成は底の射列を変えない。 -/
lemma weightedConePrecompositionMap_projection (F : I ⥤ C) (x z : C) :
    weightedConePrecompositionMap F x z ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor))
        (SimplicialCategory.sHom x z).op ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor) := rfl

/-- 係数の前合成後の初区間は、元の係数とパラメータの同じ初区間への制限の合成。 -/
lemma weightedConePrecompositionMap_coefficient (F : I ⥤ C) (x z : C) {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor)) _⦋n⦌)
    (a : (SimplicialCategory.sHom x z).op _⦋n⦌) (j : Fin (n + 1)) :
    ((weightedConePrecompositionMap F x z).app (Opposite.op ⦋n⦌) (s, a)).2.app j =
      lift (s.2.app j)
        (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
          SSet.yonedaEquiv.symm a) ≫
        (Functor.Monoidal.μIso SSet.opFunctor
          (SimplicialCategory.sHom z (F.obj (s.1.obj j))) (SimplicialCategory.sHom x z)).hom ≫
          SSet.opFunctor.map ((β_ (SimplicialCategory.sHom z (F.obj (s.1.obj j)))
            (SimplicialCategory.sHom x z)).hom ≫ eComp SSet x z (F.obj (s.1.obj j))) := by
  rfl

/-- 前合成後の cone simplex の Hom 作用は、path の最小点で評価した二係数の豊穣合成。 -/
lemma weightedCoherentCoefficient_precomposition (F : I ⥤ C) (x z : C) {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor)) _⦋n⦌)
    (a : (SimplicialCategory.sHom x z).op _⦋n⦌) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient
        ((weightedConePrecompositionMap F x z).app (Opposite.op ⦋n⦌) (s, a)).2 j =
      lift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient s.2 j)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j ≫
          SSet.opFunctor.map (stdSimplex.map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (SSet.yonedaEquiv.symm a)) ≫
        (β_ (SimplicialCategory.sHom z (F.obj (s.1.obj j)))
          (SimplicialCategory.sHom x z)).hom ≫ eComp SSet x z (F.obj (s.1.obj j)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient
  rw [weightedConePrecompositionMap_coefficient]
  erw [reflectedSimplexMap_pair_comp]
  erw [comp_lift_assoc]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
