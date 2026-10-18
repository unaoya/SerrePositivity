module

public import SerrePositivity.InfinityCategories.HomotopyLimits.KanOppositeEquivalence
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeOriginalEndFiber

/-!
概要：三形状の strict な錐への pinched Hom と元の q_x の反転なしの導来 fiber の直接比較。
方針：構成済みの反転を含む fiber の同値に、Kan 複体の反転を外す実際の同値を合成する。
規約：ULift は対象と Hom の宇宙を揃えるため fiber 全体に置く。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、A3d による元の導来 fiber の検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：Kan 複体の反転を外す同値は任意の宇宙の持ち上げの後でも同値。
方針：元の宇宙での実際のホモトピー同値を ULift で写す。
規約：空の Kan 複体も含む。追加の選択の自然性は主張しない。
使われ方：導来 fiber 全体の反転を外して pinched Hom の宇宙に揃える。 -/
def uliftKanOppositeEquivalence (K : SSet.{u}) [KanComplex K] :
    QCatEquivalence ((SSet.uliftFunctor.{v, u}).obj K.op)
      ((SSet.uliftFunctor.{v, u}).obj K) :=
  (DoldKanComparison.ulift_homotopyEquivalence.{u, v}
    (kanOppositeComparison_homotopyEquivalence K)).isQCatEquivalence.choose

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

local instance strictDirectFiber_homDiagramKan
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (F : I ⥤ C) (x : C) :
    ∀ i, KanComplex ((simplicialHomDiagram F x).obj i) :=
  fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)))

local instance strictDirectFiber_opDiagramKan (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] :
    ∀ i, KanComplex ((H ⋙ SSet.opFunctor).obj i) :=
  fun i ↦ inferInstanceAs (KanComplex (H.obj i).op)

local instance strictDirectFiber_holimKan (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] :
    KanComplex (bousfieldKanHolim H) := bousfieldKanHolim_kanComplex H

local instance strictDirectFiber_homConePointKan
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] {F : I ⥤ C} (c : Cone F) (x : C) :
    KanComplex (simplicialHomCone c x).pt := inferInstanceAs (KanComplex (SimplicialCategory.sHom x
      c.pt))

local instance strictDirectFiber_opConePointKan {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] : KanComplex (SSet.opFunctor.mapCone c).pt :=
  inferInstanceAs (KanComplex c.pt.op)

local instance strictDirectFiber_opCospanFibration (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    Fibration ((H ⋙ SSet.opFunctor).map (AsSmall.up.map WalkingCospan.Hom.inl)) :=
  fibration_opFunctor_map _

local instance strictDirectFiber_opTowerFibration (H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u})
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    ∀ n : ℕ, Fibration ((H ⋙ SSet.opFunctor).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) := fun _ ↦ fibration_opFunctor_map _

/-- 概要：strict な錐への pinched Hom は元の非反転 q_x の反転なしの導来 fiber の ULift と同値。
方針：元の比較の fiber の反転までの同値に Kan な fiber の反転を外す実際の同値を合成する。
規約：一般形は比較入力を明示し、三形状では既存の定理で全て検証する。
使われ方：HTT 4.2.4.1、A3d の可縮性判定と元の比較射の導来 fiber の直接の接続。 -/
def strictConePinched_originalFiberEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : I ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F))
    [KanComplex (limit (simplicialHomDiagram F (coherentNerveObject d.vertex)))]
    (hκ : IsSimplicialHomotopyEquivalence
      (reflectedHomHolimConeComparison F (coherentNerveObject d.vertex)))
    (hL : IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison
      (simplicialHomDiagram F (coherentNerveObject d.vertex))))
    (hL' : IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison
      (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor))) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (strictConeOriginalEndPoint d hκ hL'))) := by
  exact (strictConePinched_originalEndDerivedFiberEquivalence c d hκ hL hL').trans
    (uliftKanOppositeEquivalence _)

/-- 概要：strict な錐への pinched Hom は元の非反転 q_x の反転なしの導来 fiber の ULift と同値。
方針：元の比較の fiber の反転までの同値に Kan な fiber の反転を外す実際の同値を合成する。
規約：一般形は比較入力を明示し、三形状では既存の定理で全て検証する。
使われ方：HTT 4.2.4.1、A3d の可縮性判定と元の比較射の導来 fiber の直接の接続。 -/
def strictConePinched_originalFiber_discrete_equivalence {J : Type u}
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (Discrete J) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (strictConeOriginalEndPoint d
            (reflectedHomHolimConeComparison_discrete_homotopyEquivalence F
            (coherentNerveObject d.vertex))
            (bousfieldKanLimitComparison_discrete_homotopyEquivalence
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor))))) := by
  exact (strictConePinched_originalEnd_discrete_equivalence c d).trans
    (uliftKanOppositeEquivalence _)

/-- 概要：strict な錐への pinched Hom は元の非反転 q_x の反転なしの導来 fiber の ULift と同値。
方針：元の比較の fiber の反転までの同値に Kan な fiber の反転を外す実際の同値を合成する。
規約：一般形は比較入力を明示し、三形状では既存の定理で全て検証する。
使われ方：HTT 4.2.4.1、A3d の可縮性判定と元の比較射の導来 fiber の直接の接続。 -/
def strictConePinched_originalFiber_cospan_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} WalkingCospan) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F))
    [Fibration ((simplicialHomDiagram F (coherentNerveObject d.vertex)).map
      (AsSmall.up.map WalkingCospan.Hom.inl))] :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (strictConeOriginalEndPoint d (reflectedHomHolimConeComparison_cospan_homotopyEquivalence
            F
            (coherentNerveObject d.vertex))
            (bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor) (limit.cone _)
              (limit.isLimit _))))) := by
  exact (strictConePinched_originalEnd_cospan_equivalence c d).trans
    (uliftKanOppositeEquivalence _)

/-- 概要：strict な錐への pinched Hom は元の非反転 q_x の反転なしの導来 fiber の ULift と同値。
方針：元の比較の fiber の反転までの同値に Kan な fiber の反転を外す実際の同値を合成する。
規約：一般形は比較入力を明示し、三形状では既存の定理で全て検証する。
使われ方：HTT 4.2.4.1、A3d の可縮性判定と元の比較射の導来 fiber の直接の接続。 -/
def strictConePinched_originalFiber_tower_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} ℕᵒᵖ) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F))
    [∀ n : ℕ, Fibration ((simplicialHomDiagram F (coherentNerveObject d.vertex)).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (strictConeOriginalEndPoint d (reflectedHomHolimConeComparison_tower_homotopyEquivalence F
            (coherentNerveObject d.vertex))
            (bousfieldKanLimitComparison_tower_homotopyEquivalence
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor))))) := by
  exact (strictConePinched_originalEnd_tower_equivalence c d).trans
    (uliftKanOppositeEquivalence _)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
