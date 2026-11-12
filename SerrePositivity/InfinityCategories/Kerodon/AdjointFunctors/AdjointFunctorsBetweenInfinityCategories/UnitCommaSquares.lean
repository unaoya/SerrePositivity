module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberExtension
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalFunctorMap

/-!
概要：comma fiber の写像空間の族を X のホモトピーの正方形として記述する。
方針：固定始域の族の全単射を区間の両端条件と両立させる。
規約：X,Y やパラメータに quasicategory 性を仮定せず、厳密な全単射を構成する。
使われ方：Kerodon §6.2.6（Tag 02FQ） の普遍矢印の写像空間と導来 fiber の比較の始域。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：comma fiber の族の制限の等式は二つの成分の等式で判定できる。
方針：標的・ホモトピーの前合成公式と外延性を使う。
規約：制限する射 i は任意。
使われ方：区間の端点条件を正方形の側辺条件へ移す。 -/
lemma unitCommaFiber_precomp_eq_iff {A B X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} (i : A ⟶ B) (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)
    (g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) :
    i ≫ f = g ↔
      i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget f = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget g ∧
      (i ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f).h =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy g).h := by
  constructor
  · intro h
    constructor
    · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget_precomp, h]
    · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy_precomp, h]
  · rintro ⟨hb, hH⟩
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber_hom_ext
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget_precomp]
      exact hb
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy_precomp]
      exact hH

/-- 概要：comma fiber の二頂点を結ぶ正方形のパラメータ付きデータ。
方針：Y の区間図式と X のホモトピーを保持し、両側辺を固定する。
規約：ホモトピーの区間は第二因子、写像空間の区間は第一因子。
使われ方：写像空間比較を導来 fiber と同定するための具体的な図式。 -/
structure UnitCommaFiberSquare {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌)
    (v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) (A : SSet.{u}) where
  target : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y
  coherence : SSet.Homotopy (SSet.const x) (target ≫ G)
  target_zero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ target =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget (SSet.const v : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)
  target_one : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ target =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget (SSet.const w : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)
  coherence_zero : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ▷ (Δ[1] : SSet.{u})) ≫ coherence.h =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const v : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)).h
  coherence_one : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ▷ (Δ[1] : SSet.{u})) ≫ coherence.h =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const w : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)).h

/-- 概要：正方形を comma fiber の区間図式へ戻す。
方針：族を curry し、二成分の公式で側辺の等式を証明する。
規約：正方形の二つの区間を交換しない。
使われ方：写像空間の族の逆構成。 -/
noncomputable def UnitCommaFiberSquare.diagram {X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    (s : UnitCommaFiberSquare G x v w A) :
    (Δ[1] : SSet.{u}) ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry G x s.target s.coherence

/-- 概要：正方形から得た comma 図式の零端は v に定値。
方針：標的とホモトピーの二成分で判定する。
規約：厳密な等式。
使われ方：写像空間への curry の始点条件。 -/
lemma UnitCommaFiberSquare.diagram_zero {X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    (s : UnitCommaFiberSquare G x v w A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ s.diagram = SSet.const v := by
  apply (unitCommaFiber_precomp_eq_iff _ _ _).mpr
  exact ⟨by simpa only [UnitCommaFiberSquare.diagram, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_target]
    using s.target_zero,
    by simpa only [UnitCommaFiberSquare.diagram, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_homotopy]
      using s.coherence_zero⟩

/-- 概要：正方形から得た comma 図式の一端は w に定値。
方針：標的とホモトピーの二成分で判定する。
規約：厳密な等式。
使われ方：写像空間への curry の終点条件。 -/
lemma UnitCommaFiberSquare.diagram_one {X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    (s : UnitCommaFiberSquare G x v w A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ s.diagram = SSet.const w := by
  apply (unitCommaFiber_precomp_eq_iff _ _ _).mpr
  exact ⟨by simpa only [UnitCommaFiberSquare.diagram, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_target]
    using s.target_one,
    by simpa only [UnitCommaFiberSquare.diagram, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_homotopy]
      using s.coherence_one⟩

/-- 概要：comma fiber の写像空間の族を正方形へ展開する。
方針：区間図式を展開し、その標的とホモトピーを取り出す。
規約：端点は区間模型の端点条件から回収する。
使われ方：普遍矢印の写像空間の具体的表示。 -/
noncomputable def unitCommaFiberMappingSquare {A X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace v w) : UnitCommaFiberSquare G x v w A where
  target := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f)
  coherence := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f)
  target_zero := ((unitCommaFiber_precomp_eq_iff _ _ _).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_zero f)).1
  target_one := ((unitCommaFiber_precomp_eq_iff _ _ _).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_one f)).1
  coherence_zero := ((unitCommaFiber_precomp_eq_iff _ _ _).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_zero f)).2
  coherence_one := ((unitCommaFiber_precomp_eq_iff _ _ _).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_one f)).2

/-- 概要：正方形は標的とホモトピーの射で決まる。
方針：標的の等式を消去し、ホモトピーの外延性と証明無関係性を使う。
規約：側辺条件の証明の選び方に依存しない。
使われ方：写像空間の族との全単射の両逆。 -/
lemma UnitCommaFiberSquare.ext {X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    {s t : UnitCommaFiberSquare G x v w A} (hb : s.target = t.target)
    (hH : s.coherence.h = t.coherence.h) : s = t := by
  cases s with
  | mk b H hb₀ hb₁ hH₀ hH₁ =>
    cases t with
    | mk c K hc₀ hc₁ hK₀ hK₁ =>
      dsimp only at hb hH
      subst c
      have hk : H = K := RelativeMorphism.Homotopy.ext hH
      subst K
      rfl

/-- 概要：comma fiber の写像空間の任意の族と、側辺を固定した正方形の厳密な全単射。
方針：comma の族と区間模型の curry の二つの全単射を端点条件に制限する。
規約：quasicategory 性を仮定せず、同値はホモトピー類の商ではない。
使われ方：局所存在判定で写像空間を導来 fiber に比較するための表示。 -/
noncomputable def unitCommaFiberMappingSquareEquiv {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace v w) ≃ UnitCommaFiberSquare G x v w A where
  toFun := unitCommaFiberMappingSquare
  invFun s := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyCurry s.diagram s.diagram_zero s.diagram_one
  left_inv f := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective v w
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyUncurry_curry]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_homotopyFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f)
  right_inv s := by
    apply UnitCommaFiberSquare.ext
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyCurry s.diagram s.diagram_zero s.diagram_one)) = s.target
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyUncurry_curry]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_target G x s.target s.coherence
    · change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyCurry s.diagram s.diagram_zero s.diagram_one))).h = s.coherence.h
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyUncurry_curry]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_homotopy G x s.target s.coherence

/-- 概要：正方形の標的図式は comma の標的射影による写像空間の作用を表す。
方針：区間写像空間の作用を展開し、射影の合成を結合し直す。
規約：写像空間の比較は実際の単体集合の射による。
使われ方：正方形と単位比較の導来 fiber を底の写像空間上で比較する。 -/
lemma unitCommaFiberMappingSquare_target {A X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace v w) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G) v w) =
        (unitCommaFiberMappingSquare f).target := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap_uncurry]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
