module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CartesianEdgeInterchange
public import SerrePositivity.InfinityCategories.Kan.TriangleDiamondComposition

/-! # 元の二つの全辺からの実交換三角形対
概要：二辺を二つの順序で辿る実三角形を、同じ全対角辺を持つ実三角形対に束ねる。
方針：元の二辺の恒等合成三角形の直積を同じ写像で写す。
規約：全二単体は元の二辺の同じ退化面の像であり、充填を行わない。
使われ方：元の BF 比較辺と最後の raw 補正の全実交換面。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
variable {K L M : SSet.{u}} {x₀ x₁ : K _⦋0⦌} {y₀ y₁ : L _⦋0⦌}
  (e : K.Edge x₀ x₁) (f : L.Edge y₀ y₁) (p : K ⊗ L ⟶ M)

/-- 第一因子を先に動かす経路の元の全下辺。 -/
def cartesianInterchangeFirstLower (e : K.Edge x₀ x₁)
    (_f : L.Edge y₀ y₁) (p : K ⊗ L ⟶ M) := (_root_.SerrePositivity.InfinityCategories.Kan.cartesianEdgePair e (SSet.Edge.id y₀)).map p

/-- 第一因子を先に動かす経路の元の全上辺。 -/
def cartesianInterchangeFirstUpper (_e : K.Edge x₀ x₁)
    (f : L.Edge y₀ y₁) (p : K ⊗ L ⟶ M) := (_root_.SerrePositivity.InfinityCategories.Kan.cartesianEdgePair (SSet.Edge.id x₁) f).map p

/-- 第二因子を先に動かす経路の元の全下辺。 -/
def cartesianInterchangeSecondLower (_e : K.Edge x₀ x₁)
    (f : L.Edge y₀ y₁) (p : K ⊗ L ⟶ M) := (_root_.SerrePositivity.InfinityCategories.Kan.cartesianEdgePair (SSet.Edge.id x₀) f).map p

/-- 第二因子を先に動かす経路の元の全上辺。 -/
def cartesianInterchangeSecondUpper (e : K.Edge x₀ x₁)
    (_f : L.Edge y₀ y₁) (p : K ⊗ L ⟶ M) := (_root_.SerrePositivity.InfinityCategories.Kan.cartesianEdgePair e (SSet.Edge.id y₁)).map p

/-- 元の二辺を二順序で辿り、同じ全対角辺へ至る実交換三角形対。 -/
def cartesianInterchangeDiamond : _root_.SerrePositivity.InfinityCategories.Kan.CompositionDiamond
    (_root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeFirstLower e f p) (_root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeFirstUpper e f p)
    (_root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeSecondLower e f p) (_root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeSecondUpper e f p) where
  _root_.SerrePositivity.InfinityCategories.Kan.CompositionDiamond.diagonal := (_root_.SerrePositivity.InfinityCategories.Kan.cartesianEdgePair e f).map p
  _root_.SerrePositivity.InfinityCategories.Kan.CompositionDiamond.first := (_root_.SerrePositivity.InfinityCategories.Kan.cartesianEdgeLowerTriangle e f).map p
  _root_.SerrePositivity.InfinityCategories.Kan.CompositionDiamond.second := (_root_.SerrePositivity.InfinityCategories.Kan.cartesianEdgeUpperTriangle e f).map p

/-- 第一全二単体は、元の二辺の同じ退化三角形の積の像そのもの。 -/
lemma cartesianInterchangeDiamond_first :
    (_root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeDiamond e f p).first.simplex =
      p.app (Opposite.op ⦋2⦌) (K.σ 1 e.edge, L.σ 0 f.edge) := rfl

/-- 第二全二単体も、元の同じ二辺の退化三角形の積の像そのもの。 -/
lemma cartesianInterchangeDiamond_second :
    (_root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeDiamond e f p).second.simplex =
      p.app (Opposite.op ⦋2⦌) (K.σ 0 e.edge, L.σ 1 f.edge) := rfl

/-- 共通対角辺も、元の両全辺の同時合成の像そのもの。 -/
lemma cartesianInterchangeDiamond_diagonal :
    (_root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeDiamond e f p).diagonal.edge =
      p.app (Opposite.op ⦋1⦌) (e.edge, f.edge) := rfl

/-- 同じ元の二実三角形から、両経路の同じ合成を回収する。 -/
lemma cartesianInterchangeDiamond_comp :
    SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeFirstLower e f p) ≫
        SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeFirstUpper e f p) =
      SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeSecondLower e f p) ≫
        SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeSecondUpper e f p) :=
  (SSet.HomotopyCategory.homMk_comp_homMk (_root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeDiamond e f p).first).trans
    (SSet.HomotopyCategory.homMk_comp_homMk (_root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeDiamond e f p).second).symm

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeDiamond (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianInterchangeDiamond := _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeDiamond

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianInterchangeDiamond_comp := _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeDiamond_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianInterchangeDiamond_diagonal := _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeDiamond_diagonal

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianInterchangeDiamond_first := _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeDiamond_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianInterchangeDiamond_second := _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeDiamond_second

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeFirstLower (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianInterchangeFirstLower := _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeFirstLower

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeFirstUpper (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianInterchangeFirstUpper := _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeFirstUpper

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeSecondLower (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianInterchangeSecondLower := _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeSecondLower

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeSecondUpper (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianInterchangeSecondUpper := _root_.SerrePositivity.InfinityCategories.Kan.cartesianInterchangeSecondUpper
