module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.KanOppositeEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.StrictConeOriginalEndFiber

/-!
概要：三形状の strict な錐への pinched Hom と元の q_x の反転なしの導来 fiber の直接比較。
方針：構成済みの反転を含む fiber の同値に、Kan 複体の反転を外す実際の同値を合成する。
規約：ULift は対象と Hom の宇宙を揃えるため fiber 全体に置く。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS）・7.5.4.6（Tag 03BB）、A3d による元の導来 fiber の検出。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
noncomputable section

/-- 概要：Kan 複体の反転を外す同値は任意の宇宙の持ち上げの後でも同値。
方針：元の宇宙での実際のホモトピー同値を ULift で写す。
規約：空の Kan 複体も含む。追加の選択の自然性は主張しない。
使われ方：導来 fiber 全体の反転を外して pinched Hom の宇宙に揃える。 -/
def uliftKanOppositeEquivalence (K : SSet.{u}) [KanComplex K] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{v, u}).obj K.op)
      ((SSet.uliftFunctor.{v, u}).obj K) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence.{u, v}
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanOppositeComparison_homotopyEquivalence K)).isQCatEquivalence.choose

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

local instance strictDirectFiber_homDiagramKan
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (F : I ⥤ C) (x : C) :
    ∀ i, KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).obj i) :=
  fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)))

local instance strictDirectFiber_opDiagramKan (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] :
    ∀ i, KanComplex ((H ⋙ SSet.opFunctor).obj i) :=
  fun i ↦ inferInstanceAs (KanComplex (H.obj i).op)

local instance strictDirectFiber_holimKan (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex H

local instance strictDirectFiber_homConePointKan
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] {F : I ⥤ C} (c : Cone F) (x : C) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x).pt := inferInstanceAs (KanComplex (SimplicialCategory.sHom x
      c.pt))

local instance strictDirectFiber_opConePointKan {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] : KanComplex (SSet.opFunctor.mapCone c).pt :=
  inferInstanceAs (KanComplex c.pt.op)

local instance strictDirectFiber_opCospanFibration (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    Fibration ((H ⋙ SSet.opFunctor).map (AsSmall.up.map WalkingCospan.Hom.inl)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.fibration_opFunctor_map _

local instance strictDirectFiber_opTowerFibration (H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u})
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    ∀ n : ℕ, Fibration ((H ⋙ SSet.opFunctor).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) := fun _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.fibration_opFunctor_map _

/-- 概要：strict な錐への pinched Hom は元の非反転 q_x の反転なしの導来 fiber の ULift と同値。
方針：元の比較の fiber の反転までの同値に Kan な fiber の反転を外す実際の同値を合成する。
規約：一般形は比較入力を明示し、三形状では既存の定理で全て検証する。
使われ方：HTT 4.2.4.1、A3d の可縮性判定と元の比較射の導来 fiber の直接の接続。 -/
def strictConePinched_originalFiberEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : I ⥤ C} (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F))
    [KanComplex (limit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)))]
    (hκ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)))
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))))
    (hL' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex) ⋙ SSet.opFunctor))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictConeOriginalEndPoint d hκ hL'))) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictConePinched_originalEndDerivedFiberEquivalence c d hκ hL hL').trans
    (uliftKanOppositeEquivalence _)

/-- 概要：strict な錐への pinched Hom は元の非反転 q_x の反転なしの導来 fiber の ULift と同値。
方針：元の比較の fiber の反転までの同値に Kan な fiber の反転を外す実際の同値を合成する。
規約：一般形は比較入力を明示し、三形状では既存の定理で全て検証する。
使われ方：HTT 4.2.4.1、A3d の可縮性判定と元の比較射の導来 fiber の直接の接続。 -/
def strictConePinched_originalFiber_discrete_equivalence {J : Type u}
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (Discrete J) ⥤ C} (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictConeOriginalEndPoint d
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_discrete_homotopyEquivalence F
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_discrete_homotopyEquivalence
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex) ⋙ SSet.opFunctor))))) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictConePinched_originalEnd_discrete_equivalence c d).trans
    (uliftKanOppositeEquivalence _)

/-- 概要：strict な錐への pinched Hom は元の非反転 q_x の反転なしの導来 fiber の ULift と同値。
方針：元の比較の fiber の反転までの同値に Kan な fiber の反転を外す実際の同値を合成する。
規約：一般形は比較入力を明示し、三形状では既存の定理で全て検証する。
使われ方：HTT 4.2.4.1、A3d の可縮性判定と元の比較射の導来 fiber の直接の接続。 -/
def strictConePinched_originalFiber_cospan_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} WalkingCospan) ⥤ C} (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F))
    [Fibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)).map
      (AsSmall.up.map WalkingCospan.Hom.inl))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictConeOriginalEndPoint d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_cospan_homotopyEquivalence
            F
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex) ⋙ SSet.opFunctor) (limit.cone _)
              (limit.isLimit _))))) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictConePinched_originalEnd_cospan_equivalence c d).trans
    (uliftKanOppositeEquivalence _)

/-- 概要：strict な錐への pinched Hom は元の非反転 q_x の反転なしの導来 fiber の ULift と同値。
方針：元の比較の fiber の反転までの同値に Kan な fiber の反転を外す実際の同値を合成する。
規約：一般形は比較入力を明示し、三形状では既存の定理で全て検証する。
使われ方：HTT 4.2.4.1、A3d の可縮性判定と元の比較射の導来 fiber の直接の接続。 -/
def strictConePinched_originalFiber_tower_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} ℕᵒᵖ) ⥤ C} (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F))
    [∀ n : ℕ, Fibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictConeOriginalEndPoint d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_tower_homotopyEquivalence F
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_tower_homotopyEquivalence
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex) ⋙ SSet.opFunctor))))) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictConePinched_originalEnd_tower_equivalence c d).trans
    (uliftKanOppositeEquivalence _)

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
