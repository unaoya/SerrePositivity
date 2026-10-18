module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeFiberReflection
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeSmallReflectedFiber

/-!
概要：三形状の strict な錐への pinched Hom と元の非反転 q_x の導来 fiber の反転の直接比較。
方針：反転比較の fiber の模型を元の比較の fiber の反転へ移し、その同値を ULift で写す。
規約：fiber 全体の反転と宇宙の持ち上げを明示し、比較射自体は元の q_x を使う。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、A3d による元の比較の fiber の検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

local instance strictOriginalEnd_homDiagramKan
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (F : I ⥤ C) (x : C) :
    ∀ i, KanComplex ((simplicialHomDiagram F x).obj i) :=
  fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)))

local instance strictOriginalEnd_opDiagramKan (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] :
    ∀ i, KanComplex ((H ⋙ SSet.opFunctor).obj i) :=
  fun i ↦ inferInstanceAs (KanComplex (H.obj i).op)

local instance strictOriginalEnd_holimKan (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] :
    KanComplex (bousfieldKanHolim H) := bousfieldKanHolim_kanComplex H

local instance strictOriginalEnd_homConePointKan
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] {F : I ⥤ C} (c : Cone F) (x : C) :
    KanComplex (simplicialHomCone c x).pt := inferInstanceAs (KanComplex (SimplicialCategory.sHom x
      c.pt))

local instance strictOriginalEnd_opConePointKan {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] : KanComplex (SSet.opFunctor.mapCone c).pt :=
  inferInstanceAs (KanComplex c.pt.op)

local instance strictOriginalEnd_opCospanFibration (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    Fibration ((H ⋙ SSet.opFunctor).map (AsSmall.up.map WalkingCospan.Hom.inl)) :=
  fibration_opFunctor_map _

local instance strictOriginalEnd_opTowerFibration (H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u})
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    ∀ n : ℕ, Fibration ((H ⋙ SSet.opFunctor).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) := fun _ ↦ fibration_opFunctor_map _

/-- 概要：coherent な錐の標準点から回収した元の非反転 end の点。
方針：元の宇宙の反転 end の点を、反転係数の fiber の比較で元の end へ移す。
規約：二つの同値の逆の選択を含み、元の錐 d に付随する点を保持する。
使われ方：元の q_x の導来 fiber の固定点。 -/
def strictConeOriginalEndPoint {F : I ⥤ C} (d : JoinCone (strictCoherentDiagram F))
    (hκ : IsSimplicialHomotopyEquivalence
      (reflectedHomHolimConeComparison F (coherentNerveObject d.vertex)))
    (hL' : IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison
      (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor))) :
    (bousfieldKanHolim (simplicialHomDiagram F (coherentNerveObject d.vertex))) _⦋0⦌ :=
  bousfieldKanReflectedFiberPoint _ hL' (strictConeSmallReflectedEndPoint d hκ)

/-- 概要：比較の同値性の入力の下で pinched Hom は元の q_x の導来 fiber の反転の ULift と同値。
方針：反転比較の fiber の同値を元の比較の fiber の反転へ移し、ULift 後に合成する。
規約：一般形は end 比較と二つの極限標準比較の同値性を入力に取る。三形状で検証する。
使われ方：HTT 4.2.4.1、元の比較射を使う実際の導来 fiber の比較。 -/
def strictConePinched_originalEndDerivedFiberEquivalence
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
          (strictConeOriginalEndPoint d hκ hL')).op) := by
  let e := bousfieldKanConeFiberReflectionEquivalence
    (simplicialHomCone c (coherentNerveObject d.vertex)) hL hL'
    (strictConeSmallReflectedEndPoint d hκ)
  have he := e.isQCatEquivalence.isSimplicialHomotopyEquivalence
  let e' := (DoldKanComparison.ulift_homotopyEquivalence.{u, v} he).isQCatEquivalence.choose
  exact (strictConePinched_smallReflectedEndDerivedFiberEquivalence c d hκ).trans e'

/-- 概要：discrete の strict な錐への pinched Hom は元の q_x の導来 fiber の反転の ULift と同値。
方針：この形状の end 比較・極限標準比較を検証し、元の比較の fiber への同値を合成する。
規約：局所 Kan 性と指定形状の fibration 条件を使い、錐 c 自体の極限性は要求しない。
使われ方：HTT 4.2.4.1、A3d から元の非反転の比較射の導来 fiber の検出。 -/
def strictConePinched_originalEnd_discrete_equivalence {J : Type u}
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
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor)))).op) := by
  exact strictConePinched_originalEndDerivedFiberEquivalence c d
    (reflectedHomHolimConeComparison_discrete_homotopyEquivalence F
            (coherentNerveObject d.vertex))
    (bousfieldKanLimitComparison_discrete_homotopyEquivalence (simplicialHomDiagram F
      (coherentNerveObject d.vertex)))
    (bousfieldKanLimitComparison_discrete_homotopyEquivalence
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor))

/-- 概要：cospan の strict な錐への pinched Hom は元の q_x の導来 fiber の反転の ULift と同値。
方針：この形状の end 比較・極限標準比較を検証し、元の比較の fiber への同値を合成する。
規約：局所 Kan 性と指定形状の fibration 条件を使い、錐 c 自体の極限性は要求しない。
使われ方：HTT 4.2.4.1、A3d から元の非反転の比較射の導来 fiber の検出。 -/
def strictConePinched_originalEnd_cospan_equivalence
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
              (limit.isLimit _)))).op) := by
  let H := simplicialHomDiagram F (coherentNerveObject d.vertex)
  let U := (Functor.const (AsSmall.{u} WalkingCospan)).obj (Δ[0] : SSet.{u})
  have : Mono (U.map (AsSmall.up.map WalkingCospan.Hom.inr)) := by
    change Mono (𝟙 (Δ[0] : SSet.{u}))
    infer_instance
  have : KanComplex (weightedSections U H) := weightedSections_cospan_leftFibration_kanComplex U H
  have : KanComplex (limit H) := strictLimit_kanComplex_of_terminalWeight U H
    (weightIsTerminalOfObj U (fun _ ↦ stdSimplex.isTerminalObj₀))
  exact strictConePinched_originalEndDerivedFiberEquivalence c d
    (reflectedHomHolimConeComparison_cospan_homotopyEquivalence F
            (coherentNerveObject d.vertex))
    (bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence
      (simplicialHomDiagram F (coherentNerveObject d.vertex)) (limit.cone _) (limit.isLimit _))
    (bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor) (limit.cone _)
              (limit.isLimit _))

/-- 概要：tower の strict な錐への pinched Hom は元の q_x の導来 fiber の反転の ULift と同値。
方針：この形状の end 比較・極限標準比較を検証し、元の比較の fiber への同値を合成する。
規約：局所 Kan 性と指定形状の fibration 条件を使い、錐 c 自体の極限性は要求しない。
使われ方：HTT 4.2.4.1、A3d から元の非反転の比較射の導来 fiber の検出。 -/
def strictConePinched_originalEnd_tower_equivalence
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
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor)))).op) := by
  let H := simplicialHomDiagram F (coherentNerveObject d.vertex)
  let U := (Functor.const (AsSmall.{u} ℕᵒᵖ)).obj (Δ[0] : SSet.{u})
  have : KanComplex (weightedSections U H) := weightedSections_tower_kanComplex U H
  have : KanComplex (limit H) := strictLimit_kanComplex_of_terminalWeight U H
    (weightIsTerminalOfObj U (fun _ ↦ stdSimplex.isTerminalObj₀))
  exact strictConePinched_originalEndDerivedFiberEquivalence c d
    (reflectedHomHolimConeComparison_tower_homotopyEquivalence F
            (coherentNerveObject d.vertex))
    (bousfieldKanLimitComparison_tower_homotopyEquivalence (simplicialHomDiagram F
      (coherentNerveObject d.vertex)))
    (bousfieldKanLimitComparison_tower_homotopyEquivalence
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
