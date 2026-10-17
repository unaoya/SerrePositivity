module

public import SerrePositivity.BhattScholze.PerfectoidizationInterface.Setup
public import SerrePositivity.InfinityCategories.Derived.DiscreteEmbedding
public import SerrePositivity.InfinityCategories.Derived.HomotopyCategoryComparison
public import SerrePositivity.InfinityCategories.Core.HomotopyNatTrans
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # 界面で用いる導来対象・辺・自然変換

概要：D5b の離散埋め込みと D3 の同値を界面の名前空間へ包装する。
方針：頂点・辺を評価し、整数次数のコホモロジーを通常の導来圏で取る。
規約：自然変換は区間との積からの単体的射である。
使われ方：E3 の単位、H⁰ の環構造、制限した標的図式。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory CategoryTheory.Limits MonoidalCategory DifferentialGraded
open SerrePositivity.InfinityCategories
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- D5b の離散可換代数の埋め込みを、同じ under 圏の始域で使う。 -/
abbrev J : algebraNerve R ⟶ derivedInfinityCategory R := discreteEmbedding R

/-- 単体的関手の通常の代数における値。 -/
def vertex (F : algebraNerve R ⟶ derivedInfinityCategory R) (S : A_R R) :
    (derivedInfinityCategory R) _⦋0⦌ := F.app _ (ComposableArrows.mk₀ S)

/-- 通常の代数の射を単体的関手で写した辺。 -/
def edge (F : algebraNerve R ⟶ derivedInfinityCategory R) {S T : A_R R} (f : S ⟶ T) :
    (derivedInfinityCategory R).Edge (vertex R F S) (vertex R F T) :=
  (CategoryTheory.nerve.edgeMk f).map F

/-- D3 経由の整数次数コホモロジー関手。 -/
def HFunctor (i : ℤ) : derivedInfinityHomotopyCategory R ⥤ ModuleCat.{u} R :=
  (derivedInfinityHomotopyEquivalence R).functor ⋙ DerivedCategory.homologyFunctor _ i

/-- 導来頂点の i 次コホモロジー加群。 -/
def H (i : ℤ) (x : (derivedInfinityCategory R) _⦋0⦌) : ModuleCat.{u} R :=
  (HFunctor R i).obj ⟨x⟩

/-- 導来辺がコホモロジー上に誘導する線形射。 -/
def HMap (i : ℤ) {x y : (derivedInfinityCategory R) _⦋0⦌}
    (e : (derivedInfinityCategory R).Edge x y) : H R i x ⟶ H R i y :=
  (HFunctor R i).map (SSet.Truncated.HomotopyCategory₂.homMk e.toTruncated)

/-- D3 によるコホモロジーは、頂点の semifree 複体のコホモロジーに一致する。 -/
def HIso (i : ℤ) (x : (derivedInfinityCategory R) _⦋0⦌) :
    H R i x ≅ (derivedInfinityCategoryVertexEquiv R x).val.homology i :=
  (DerivedCategory.homologyFunctorFactorsh (ModuleCat R) i).app
      ((semifreeHomotopyComparison R).obj ((derivedInfinityH0Equivalence R).functor.obj ⟨x⟩)) ≪≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat R) (.up ℤ) i).app
      (derivedInfinityCategoryVertexEquiv R x).val

/-- 離散埋め込みの零次コホモロジーは元の R 加群。 -/
def JHZeroIso (S : A_R R) :
    H R 0 (vertex R (J R) S) ≅ (discreteAlgebraModule R).obj S :=
  HIso R 0 _ ≪≫ discreteEmbeddingHomologyZeroIso R S

/-- 離散性は零次以外の全コホモロジーの消滅。 -/
def Disc (x : (derivedInfinityCategory R) _⦋0⦌) : Prop :=
  ∀ i : ℤ, i ≠ 0 → IsZero (H R i x)

/-- 単体的自然変換。両端の等式もデータに含む。 -/
abbrev NatInfinity (F G : algebraNerve R ⟶ derivedInfinityCategory R) := SSet.Homotopy F G

/-- 自然変換の S における成分の辺。 -/
def component {F G : algebraNerve R ⟶ derivedInfinityCategory R}
    (η : NatInfinity R F G) (S : A_R R) :
    (derivedInfinityCategory R).Edge (vertex R F S) (vertex R G S) :=
  (SSet.Edge.ofTruncated
    (((SSet.Truncated.Edge.id (X := (SSet.truncation 2).obj (algebraNerve R))
      (ComposableArrows.mk₀ S)).tensor homotopyIntervalEdge).map
        ((SSet.truncation 2).map η.h))).ofEq
    (congrArg (fun (f : algebraNerve R ⟶ derivedInfinityCategory R) =>
      f.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ S)) η.h₀)
    (congrArg (fun (f : algebraNerve R ⟶ derivedInfinityCategory R) =>
      f.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ S)) η.h₁)

/-- 指定された perfectoid 標的への離散 R 代数の図式。 -/
def targetDiagram (p : ℕ) [Fact p.Prime] (S : A_R R) :
    perfectoidTargetNerve p S.right ⟶ derivedInfinityCategory R :=
  nerveMap (targetAlgebra R p S) ≫ J R

end SerrePositivity.BhattScholze.PerfectoidizationInterface
