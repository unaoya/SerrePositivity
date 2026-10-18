module

public import SerrePositivity.InfinityCategories.F1B.UnitCommaFiberExtension
public import SerrePositivity.InfinityCategories.F1B.IntervalFunctorMap

/-!
概要：comma fiber の写像空間の族を X のホモトピーの正方形として記述する。
方針：固定始域の族の全単射を区間の両端条件と両立させる。
規約：X,Y やパラメータに quasicategory 性を仮定せず、厳密な全単射を構成する。
使われ方：Kerodon §6.2.6 の普遍矢印の写像空間と導来 fiber の比較の始域。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：comma fiber の族の制限の等式は二つの成分の等式で判定できる。
方針：標的・ホモトピーの前合成公式と外延性を使う。
規約：制限する射 i は任意。
使われ方：区間の端点条件を正方形の側辺条件へ移す。 -/
lemma unitCommaFiber_precomp_eq_iff {A B X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} (i : A ⟶ B) (f : B ⟶ unitCommaFiber G x)
    (g : A ⟶ unitCommaFiber G x) :
    i ≫ f = g ↔
      i ≫ unitCommaFiberTarget f = unitCommaFiberTarget g ∧
      (i ▷ (Δ[1] : SSet.{u})) ≫ (unitCommaFiberHomotopy f).h =
        (unitCommaFiberHomotopy g).h := by
  constructor
  · intro h
    constructor
    · rw [← unitCommaFiberTarget_precomp, h]
    · rw [← unitCommaFiberHomotopy_precomp, h]
  · rintro ⟨hb, hH⟩
    apply unitCommaFiber_hom_ext
    · rw [unitCommaFiberTarget_precomp]
      exact hb
    · rw [unitCommaFiberHomotopy_precomp]
      exact hH

/-- 概要：comma fiber の二頂点を結ぶ正方形のパラメータ付きデータ。
方針：Y の区間図式と X のホモトピーを保持し、両側辺を固定する。
規約：ホモトピーの区間は第二因子、写像空間の区間は第一因子。
使われ方：写像空間比較を導来 fiber と同定するための具体的な図式。 -/
structure UnitCommaFiberSquare {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌)
    (v w : (unitCommaFiber G x) _⦋0⦌) (A : SSet.{u}) where
  target : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y
  coherence : SSet.Homotopy (SSet.const x) (target ≫ G)
  target_zero : prismEndpoint 0 A ≫ target =
    unitCommaFiberTarget (SSet.const v : A ⟶ unitCommaFiber G x)
  target_one : prismEndpoint 1 A ≫ target =
    unitCommaFiberTarget (SSet.const w : A ⟶ unitCommaFiber G x)
  coherence_zero : (prismEndpoint 0 A ▷ (Δ[1] : SSet.{u})) ≫ coherence.h =
    (unitCommaFiberHomotopy (SSet.const v : A ⟶ unitCommaFiber G x)).h
  coherence_one : (prismEndpoint 1 A ▷ (Δ[1] : SSet.{u})) ≫ coherence.h =
    (unitCommaFiberHomotopy (SSet.const w : A ⟶ unitCommaFiber G x)).h

/-- 概要：正方形を comma fiber の区間図式へ戻す。
方針：族を curry し、二成分の公式で側辺の等式を証明する。
規約：正方形の二つの区間を交換しない。
使われ方：写像空間の族の逆構成。 -/
noncomputable def UnitCommaFiberSquare.diagram {X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    (s : UnitCommaFiberSquare G x v w A) :
    (Δ[1] : SSet.{u}) ⊗ A ⟶ unitCommaFiber G x :=
  unitCommaFiberCurry G x s.target s.coherence

/-- 概要：正方形から得た comma 図式の零端は v に定値。
方針：標的とホモトピーの二成分で判定する。
規約：厳密な等式。
使われ方：写像空間への curry の始点条件。 -/
lemma UnitCommaFiberSquare.diagram_zero {X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    (s : UnitCommaFiberSquare G x v w A) :
    prismEndpoint 0 A ≫ s.diagram = SSet.const v := by
  apply (unitCommaFiber_precomp_eq_iff _ _ _).mpr
  exact ⟨by simpa only [UnitCommaFiberSquare.diagram, unitCommaFiberCurry_target]
    using s.target_zero,
    by simpa only [UnitCommaFiberSquare.diagram, unitCommaFiberCurry_homotopy]
      using s.coherence_zero⟩

/-- 概要：正方形から得た comma 図式の一端は w に定値。
方針：標的とホモトピーの二成分で判定する。
規約：厳密な等式。
使われ方：写像空間への curry の終点条件。 -/
lemma UnitCommaFiberSquare.diagram_one {X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    (s : UnitCommaFiberSquare G x v w A) :
    prismEndpoint 1 A ≫ s.diagram = SSet.const w := by
  apply (unitCommaFiber_precomp_eq_iff _ _ _).mpr
  exact ⟨by simpa only [UnitCommaFiberSquare.diagram, unitCommaFiberCurry_target]
    using s.target_one,
    by simpa only [UnitCommaFiberSquare.diagram, unitCommaFiberCurry_homotopy]
      using s.coherence_one⟩

/-- 概要：comma fiber の写像空間の族を正方形へ展開する。
方針：区間図式を展開し、その標的とホモトピーを取り出す。
規約：端点は区間模型の端点条件から回収する。
使われ方：普遍矢印の写像空間の具体的表示。 -/
noncomputable def unitCommaFiberMappingSquare {A X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (unitCommaFiber G x) _⦋0⦌}
    (f : A ⟶ intervalMappingSpace v w) : UnitCommaFiberSquare G x v w A where
  target := unitCommaFiberTarget (intervalMappingUncurry f)
  coherence := unitCommaFiberHomotopy (intervalMappingUncurry f)
  target_zero := ((unitCommaFiber_precomp_eq_iff _ _ _).mp (intervalFamily_zero f)).1
  target_one := ((unitCommaFiber_precomp_eq_iff _ _ _).mp (intervalFamily_one f)).1
  coherence_zero := ((unitCommaFiber_precomp_eq_iff _ _ _).mp (intervalFamily_zero f)).2
  coherence_one := ((unitCommaFiber_precomp_eq_iff _ _ _).mp (intervalFamily_one f)).2

/-- 概要：正方形は標的とホモトピーの射で決まる。
方針：標的の等式を消去し、ホモトピーの外延性と証明無関係性を使う。
規約：側辺条件の証明の選び方に依存しない。
使われ方：写像空間の族との全単射の両逆。 -/
lemma UnitCommaFiberSquare.ext {X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    {v w : (unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
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
    (x : X _⦋0⦌) (v w : (unitCommaFiber G x) _⦋0⦌) (A : SSet.{u}) :
    (A ⟶ intervalMappingSpace v w) ≃ UnitCommaFiberSquare G x v w A where
  toFun := unitCommaFiberMappingSquare
  invFun s := intervalFamilyCurry s.diagram s.diagram_zero s.diagram_one
  left_inv f := by
    apply intervalMappingUncurry_injective v w
    rw [intervalFamilyUncurry_curry]
    exact unitCommaFiberCurry_homotopyFamily (intervalMappingUncurry f)
  right_inv s := by
    apply UnitCommaFiberSquare.ext
    · change unitCommaFiberTarget (intervalMappingUncurry
        (intervalFamilyCurry s.diagram s.diagram_zero s.diagram_one)) = s.target
      rw [intervalFamilyUncurry_curry]
      exact unitCommaFiberCurry_target G x s.target s.coherence
    · change (unitCommaFiberHomotopy (intervalMappingUncurry
        (intervalFamilyCurry s.diagram s.diagram_zero s.diagram_one))).h = s.coherence.h
      rw [intervalFamilyUncurry_curry]
      exact unitCommaFiberCurry_homotopy G x s.target s.coherence

/-- 概要：正方形の標的図式は comma の標的射影による写像空間の作用を表す。
方針：区間写像空間の作用を展開し、射影の合成を結合し直す。
規約：写像空間の比較は実際の単体集合の射による。
使われ方：正方形と単位比較の導来 fiber を底の写像空間上で比較する。 -/
lemma unitCommaFiberMappingSquare_target {A X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (unitCommaFiber G x) _⦋0⦌}
    (f : A ⟶ intervalMappingSpace v w) :
    intervalMappingUncurry (f ≫ intervalFunctorMap
      (vertexFiberι (unitCommaSource G) x ≫ unitCommaTarget G) v w) =
        (unitCommaFiberMappingSquare f).target := by
  rw [intervalFunctorMap_uncurry]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories
