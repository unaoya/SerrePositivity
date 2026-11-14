module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.OppositeComparisonFiber
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.ComparisonFiberPostIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ComparisonFiberBasePoint
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeComparisonReflection

/-!
概要：三形状の元の錐の比較と反転した錐の比較の実際の導来 fiber の同値。
方針：二つの比較を厳密極限への射で分解し、極限保存同型と標準比較の同値で fiber を移す。
規約：fiber 自体の反転を明示し、同値性の判定だけでなく実際の fiber を比較する。
使われ方：HTT 4.2.4.1、反転した q′ の模型から元の非反転 q_x の fiber へ戻す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section

local instance coneFiberReflection_opEquivalence : SSet.opFunctor.{u}.IsEquivalence :=
  SSet.opEquivalence.isEquivalence_functor

local instance coneFiberReflection_opDiagramKan {I : Type u} [SmallCategory I]
    (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] :
    ∀ i, KanComplex ((H ⋙ SSet.opFunctor).obj i) :=
  fun i ↦ inferInstanceAs (KanComplex (H.obj i).op)

local instance coneFiberReflection_opConeKan {I : Type u} [SmallCategory I]
    {H : I ⥤ SSet.{u}} (c : Cone H) [KanComplex c.pt] :
    KanComplex (SSet.opFunctor.mapCone c).pt := inferInstanceAs (KanComplex c.pt.op)

local instance coneFiberReflection_holimKan {I : Type u} [SmallCategory I]
    (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex H

local instance coneFiberReflection_opCospanFibration
    (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    Fibration ((H ⋙ SSet.opFunctor).map (AsSmall.up.map WalkingCospan.Hom.inl)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.fibration_opFunctor_map _

local instance coneFiberReflection_opTowerFibration (H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u})
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    ∀ n : ℕ, Fibration ((H ⋙ SSet.opFunctor).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) := fun _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.fibration_opFunctor_map _

/-- 概要：反転した end の点から元の比較の底の点を回収する。
方針：反転した極限標準比較の逆、極限保存同型の逆、元の標準比較の反転を順に使う。
規約：最後に零次の反転の全単射で元の宇宙の元の end の点に戻す。
使われ方：反転した比較の fiber と元の比較の fiber の固定点の整合性。 -/
def bousfieldKanReflectedFiberPoint {I : Type u} [SmallCategory I] (H : I ⥤ SSet.{u})
    (hκ' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison (H ⋙ SSet.opFunctor)))
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) _⦋0⦌ :=
  SSet.opObjEquiv ((SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H)).app _
    ((preservesLimitIso SSet.opFunctor H).inv.app _ ((Classical.choose hκ').app _ b)))

/-- 概要：両極限標準比較が同値なら反転した錐の比較の fiber と元の fiber の反転は同値。
方針：厳密極限への射の反転の可換式と、標的の同値・同型による fiber の移送を合成する。
規約：錐 c 自体の極限性は不要。一般形では二つの標準比較の同値性を明示する。
使われ方：HTT 4.2.4.1、指定三形状の元の非反転比較の fiber への直接比較。 -/
def bousfieldKanConeFiberReflectionEquivalence {I : Type u} [SmallCategory I]
    {H : I ⥤ SSet.{u}} (c : Cone H) [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    [KanComplex (limit H)]
    (hκ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H))
    (hκ' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison (H ⋙ SSet.opFunctor)))
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c) (bousfieldKanReflectedFiberPoint H hκ' b)).op
        := by
  let H' := H ⋙ SSet.opFunctor
  let e := preservesLimitIso SSet.opFunctor H
  have : KanComplex (limit H') := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso e
  let a₀ := (Classical.choose hκ').app (Opposite.op ⦋0⦌) b
  let a := e.inv.app (Opposite.op ⦋0⦌) a₀
  let p := SSet.opFunctor.map (limit.lift H c)
  have hq : p ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H) =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c) := by
    rw [← CategoryTheory.Functor.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_limitLift]
  let e₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberPostInverseEquivalence
    (limit.lift H' (SSet.opFunctor.mapCone c)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H') hκ' b
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_limitLift] at e₁
  let e₂ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.comparisonFiberPostIsoEquivalence p e a₀
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (SSet.opFunctor.map (limit.lift H c) ≫
      (preservesLimitIso SSet.opFunctor H).hom) a₀) at e₂
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ReflectedConeLimitLift.reflectedConeLimitLift c] at e₂
  let e₃ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.comparisonFiberPost_homotopyEquivalence p
    (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeKanHomotopyEquivalence hκ) a).isQCatEquivalence.choose
  rw [hq] at e₃
  exact e₁.symm.trans (e₂.symm.trans (e₃.trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeComparisonFiberEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c)
      (bousfieldKanReflectedFiberPoint H hκ' b)).symm))

/-- 概要：discrete の反転した錐の比較の fiber は元の比較の fiber の反転と同値。
方針：この形状の二つの極限標準比較の同値性を一般の fiber の比較へ渡す。
規約：錐 c 自体の極限性は要求せず、指定形状の Kan と fibration の条件を使う。
使われ方：HTT 4.2.4.1、元の非反転 q_x の導来 fiber への直接比較。 -/
def bousfieldKanConeFiberReflection_discrete_equivalence {J : Type u}
    {H : (Discrete J) ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c)
        (bousfieldKanReflectedFiberPoint H (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_discrete_homotopyEquivalence
          (H ⋙ SSet.opFunctor)) b)).op := by
  exact bousfieldKanConeFiberReflectionEquivalence c
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_discrete_homotopyEquivalence H)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_discrete_homotopyEquivalence (H ⋙ SSet.opFunctor)) b

/-- 概要：cospan の反転した錐の比較の fiber は元の比較の fiber の反転と同値。
方針：この形状の二つの極限標準比較の同値性を一般の fiber の比較へ渡す。
規約：錐 c 自体の極限性は要求せず、指定形状の Kan と fibration の条件を使う。
使われ方：HTT 4.2.4.1、元の非反転 q_x の導来 fiber への直接比較。 -/
def bousfieldKanConeFiberReflection_cospan_equivalence
    {H : (AsSmall.{u} WalkingCospan) ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))]
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c)
        (bousfieldKanReflectedFiberPoint H
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence
        (H ⋙ SSet.opFunctor) (limit.cone _) (limit.isLimit _)) b)).op := by
  let U := (Functor.const (AsSmall.{u} WalkingCospan)).obj (Δ[0] : SSet.{u})
  have : Mono (U.map (AsSmall.up.map WalkingCospan.Hom.inr)) := by
    change Mono (𝟙 (Δ[0] : SSet.{u}))
    infer_instance
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections U H) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_cospan_leftFibration_kanComplex U H
  have : KanComplex (limit H) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictLimit_kanComplex_of_terminalWeight U H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightIsTerminalOfObj U (fun _ ↦ stdSimplex.isTerminalObj₀))
  exact bousfieldKanConeFiberReflectionEquivalence c
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence H
      (limit.cone H) (limit.isLimit H))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence
        (H ⋙ SSet.opFunctor) (limit.cone _) (limit.isLimit _)) b

/-- 概要：tower の反転した錐の比較の fiber は元の比較の fiber の反転と同値。
方針：この形状の二つの極限標準比較の同値性を一般の fiber の比較へ渡す。
規約：錐 c 自体の極限性は要求せず、指定形状の Kan と fibration の条件を使う。
使われ方：HTT 4.2.4.1、元の非反転 q_x の導来 fiber への直接比較。 -/
def bousfieldKanConeFiberReflection_tower_equivalence
    {H : (AsSmall.{u} ℕᵒᵖ) ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))]
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c)
        (bousfieldKanReflectedFiberPoint H (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_tower_homotopyEquivalence (H
          ⋙ SSet.opFunctor)) b)).op := by
  let U := (Functor.const (AsSmall.{u} ℕᵒᵖ)).obj (Δ[0] : SSet.{u})
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections U H) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.weightedSections_tower_kanComplex U H
  have : KanComplex (limit H) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictLimit_kanComplex_of_terminalWeight U H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightIsTerminalOfObj U (fun _ ↦ stdSimplex.isTerminalObj₀))
  exact bousfieldKanConeFiberReflectionEquivalence c
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_tower_homotopyEquivalence H)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_tower_homotopyEquivalence (H ⋙ SSet.opFunctor)) b

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
