module
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.SpaceEdgeValue
public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegEdge
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanWhiteheadComparison
public import SerrePositivity.InfinityCategories.F2.Ind.NativePreservationPosetReductionUniverse
/-!
概要：coherent filtered 空間余錐の元ごとの π 判定を Prop 値の供給境界にする。
方針：球面代表の円柱の境界に道を指定し、群の余極限を使わず基点移送を表す。
規約：π の添字 n は次数 n+1。元の全余錐・脚・transition 辺を使う。
使われ方：Ind-π の一般判定を D の評価ホモロジー計算へ代入する公開型。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial

/-- 球面の境界が指定した道をたどる、正次数 π の基点移送関係。 -/
def dgBarCompactPiTransport {X : SSet.{w}} [KanComplex X]
    (n : ℕ) {x y : X _⦋0⦌} (e : X.Edge x y)
    (a : KanHomotopyGroup X n x) (b : KanHomotopyGroup X n y) : Prop :=
  ∃ (f : X.PtSimplex (n + 1) x) (g : X.PtSimplex (n + 1) y),
    KanHomotopyGroup.mk f = a ∧ KanHomotopyGroup.mk g = b ∧
      ∃ H : SSet.Homotopy f.map g.map,
        ((SSet.boundary (n + 1)).ι ▷ (Δ[1] : SSet.{w})) ≫ H.h =
          CartesianMonoidalCategory.snd _ _ ≫ SSet.yonedaEquiv.symm e.edge

/-- 次数と基点を明示した正次数 π の写像。 -/
def dgBarCompactPiMap {X Y : SSet.{w}} [KanComplex X] [KanComplex Y]
    (n : ℕ) (f : X ⟶ Y) (x : X _⦋0⦌) :
    KanHomotopyGroup X n x → KanHomotopyGroup Y n (f.app _ x) :=
  KanHomotopyGroup.map (n := n) (x := x) f rfl

variable {I : Type u} [PartialOrder I]
  (F : (SSet.uliftFunctor.{max (u + 1) v + 1, u}).obj (nerve I) ⟶
    SpaceInfinity.{max (u + 1) v})

abbrev dgBarCompactSpaceStageVertex (i : I) :=
  F.app (Opposite.op ⦋0⦌) (ULift.up (nerveEquiv.symm i))

abbrev dgBarCompactSpaceStage (i : I) :=
  spaceInfinityObject (dgBarCompactSpaceStageVertex F i)

def dgBarCompactSpaceIndexEdge {i j : I} (hij : i ≤ j) :
    ((SSet.uliftFunctor.{max (u + 1) v + 1, u}).obj (nerve I)).Edge
      (ULift.up (nerveEquiv.symm i)) (ULift.up (nerveEquiv.symm j)) where
  edge := ULift.up (CategoryTheory.nerve.edgeMk (homOfLE hij)).edge
  src_eq := congrArg ULift.up (CategoryTheory.nerve.edgeMk (homOfLE hij)).src_eq
  tgt_eq := congrArg ULift.up (CategoryTheory.nerve.edgeMk (homOfLE hij)).tgt_eq

def dgBarCompactSpaceTransition {i j : I} (hij : i ≤ j) :
    (dgBarCompactSpaceStage F i).obj ⟶ (dgBarCompactSpaceStage F j).obj :=
  F2.spaceInfinityEdgeValue ((dgBarCompactSpaceIndexEdge.{u, v} hij).map F)

variable (c : JoinCocone F)

abbrev dgBarCompactSpaceApex := spaceInfinityObject c.vertex

def dgBarCompactSpaceLeg (i : I) :
    (dgBarCompactSpaceStage F i).obj ⟶ (dgBarCompactSpaceApex F c).obj :=
  F2.spaceInfinityEdgeValue
    (F2.Compact.coconeTransportLeg c (ULift.up (nerveEquiv.symm i)))

/-- 元ごとの π 条件を、空間と実射の抽象的な族に対して先に定義する。 -/
structure DGBarCompactSpacePiData (X : I → KanObject.{w}) (A : KanObject.{w})
    (τ : ∀ {i j : I}, i ≤ j → ((X i).obj ⟶ (X j).obj))
    (l : ∀ i : I, ((X i).obj ⟶ A.obj)) : Prop where
  components_surjective :
    ∀ z : A.obj _⦋0⦌,
    ∃ (i : I) (y : (X i).obj _⦋0⦌),
      SSet.π₀.mk ((l i).app _ y) = SSet.π₀.mk z
  components_equal_at_stage :
    ∀ (i j : I)
    (y : (X i).obj _⦋0⦌)
    (z : (X j).obj _⦋0⦌),
    SSet.π₀.mk ((l i).app _ y) =
      SSet.π₀.mk ((l j).app _ z) →
    ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
      SSet.π₀.mk ((τ hik).app _ y) =
        SSet.π₀.mk ((τ hjk).app _ z)
  positive_surjective :
    ∀ (n : ℕ) (i : I)
    (y : (X i).obj _⦋0⦌)
    (a : KanHomotopyGroup A.obj n
      ((l i).app _ y)),
    ∃ (j : I) (hij : i ≤ j)
      (b : KanHomotopyGroup (X j).obj n
        ((τ hij).app _ y)),
      ∀ e : (A.obj).Edge
        ((l j).app _ ((τ hij).app _ y))
        ((l i).app _ y),
        dgBarCompactPiTransport.{w} (X := A.obj) n e
          (dgBarCompactPiMap.{w} (X := (X j).obj)
            (Y := A.obj) n (l j)
            ((τ hij).app _ y) b) a
  positive_equal_at_stage :
    ∀ (n : ℕ) (i : I)
    (y : (X i).obj _⦋0⦌)
    (a b : KanHomotopyGroup (X i).obj n y),
    dgBarCompactPiMap.{w} (X := (X i).obj)
      (Y := A.obj) n (l i) y a =
      dgBarCompactPiMap.{w} (X := (X i).obj)
      (Y := A.obj) n (l i) y b →
    ∃ (j : I) (hij : i ≤ j),
      dgBarCompactPiMap.{w} (X := (X i).obj)
        (Y := (X j).obj) n (τ hij) y a =
        dgBarCompactPiMap.{w} (X := (X i).obj)
        (Y := (X j).obj) n (τ hij) y b
  positive_surjective_all_basepoints :
    ∀ (n : ℕ)
    (z : A.obj _⦋0⦌)
    (a : KanHomotopyGroup A.obj n z),
    ∃ (i : I) (y : (X i).obj _⦋0⦌)
      (b : KanHomotopyGroup (X i).obj n y)
      (e : (A.obj).Edge
        ((l i).app _ y) z),
      dgBarCompactPiTransport.{w} (X := A.obj) n e
        (dgBarCompactPiMap.{w} (X := (X i).obj)
          (Y := A.obj) n (l i) y b) a

/-- 元の coherent 空間図式の実辺と脚を使う、全基点の元ごとの条件。 -/
def DGBarCompactFilteredSpacePiData : Prop :=
  DGBarCompactSpacePiData (dgBarCompactSpaceStage F) (dgBarCompactSpaceApex F c)
    (fun {_ _} h => dgBarCompactSpaceTransition F h) (dgBarCompactSpaceLeg F c)

/-- Ind-π が供給する橋だけを残す Prop 値の公開入力。 -/
def DGBarCompactFilteredSpacePiBridge (κ : Cardinal.{u}) [Fact κ.IsRegular] : Prop :=
  ∀ (I : Type u) [PartialOrder I] [IsCardinalFiltered I κ]
    (F : (SSet.uliftFunctor.{max (u + 1) v + 1, u}).obj (nerve I) ⟶
      SpaceInfinity.{max (u + 1) v}) (c : JoinCocone F),
    DGBarCompactFilteredSpacePiData F c → IsColimitCone c

end SerrePositivity.InfinityCategories
