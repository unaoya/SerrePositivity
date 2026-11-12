module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.HomotopyCategoryComparison
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # 導来 ∞ 圏の零次ホモロジー

概要：D(S) の頂点と辺に零次ホモロジーを対応させる。
方針：D3 の導来同値に Mathlib の零次ホモロジー関手を合成する。
規約：辺は二次切断の辺として扱う。使われ方：D(R) 上の界面の H⁰ 同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 概要：D(S) のホモトピー圏上の零次ホモロジー関手。
方針：通常の導来圏との同値に homologyFunctor を合成する。
規約：導来圏は HasDerivedCategory で指定する。使われ方：頂点と辺の H⁰。 -/
def derivedInfinityHZeroFunctor : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S ⥤ ModuleCat.{u} S :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S).functor ⋙ DerivedCategory.homologyFunctor (ModuleCat S) 0

/-- 概要：D(S) の各頂点の零次ホモロジー加群。
方針：頂点をホモトピー圏の対象として零次関手を評価する。
規約：値は通常の S 加群。使われ方：離散入力の H⁰ 比較。 -/
def derivedInfinityHZero (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) : ModuleCat.{u} S :=
  (derivedInfinityHZeroFunctor S).obj ⟨x⟩

/-- 概要：頂点の H⁰ はその semifree 複体の通常の零次ホモロジーと同型である。
方針：Qh のホモロジー比較とホモトピー商の比較を合成する。
規約：複体の次数は整数。使われ方：頂点上の H⁰ の具体的計算。 -/
def derivedInfinityHZeroIso (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    derivedInfinityHZero S x ≅ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategoryVertexEquiv S x).val.homology 0 :=
  (DerivedCategory.homologyFunctorFactorsh (ModuleCat S) 0).app
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).obj ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor.obj ⟨x⟩)) ≪≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat S) (.up ℤ) 0).app
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategoryVertexEquiv S x).val

/-- 概要：D(S) の辺は頂点の零次ホモロジー間の射を誘導する。
方針：辺のホモトピー類に H⁰ 関手を適用する。
規約：二次切断の辺は元の単体的集合と同じ一単体を持つ。使われ方：H⁰ の射の計算。 -/
def derivedInfinityHZeroMap {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)) x y) :
    derivedInfinityHZero S x ⟶ derivedInfinityHZero S y :=
  (derivedInfinityHZeroFunctor S).map (SSet.Truncated.HomotopyCategory₂.homMk e)

/-- 概要：左ホモトピックな辺は同じ H⁰ の射を誘導する。
方針：ホモトピー圏の商での等式に関手を適用する。
規約：二次元の左ホモトピー。使われ方：辺の代表に依存しない H⁰。 -/
theorem derivedInfinityHZeroMap_homotopicL {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌}
    {e e' : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)) x y}
    (h : SSet.Truncated.HomotopicL e e') :
    derivedInfinityHZeroMap S e = derivedInfinityHZeroMap S e' :=
  congrArg (derivedInfinityHZeroFunctor S).map h.congr_homotopyCategory₂HomMk

/-- 概要：右ホモトピックな辺も同じ H⁰ の射を誘導する。
方針：右ホモトピーからホモトピー圏の等式を得る。
規約：D(S) の quasicategory 性を用いる。使われ方：左右いずれのホモトピーにも対応。 -/
theorem derivedInfinityHZeroMap_homotopicR {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌}
    {e e' : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)) x y}
    (h : SSet.Truncated.HomotopicR e e') :
    derivedInfinityHZeroMap S e = derivedInfinityHZeroMap S e' :=
  congrArg (derivedInfinityHZeroFunctor S).map h.congr_homotopyCategory₂HomMk

/-- 概要：退化した恒等辺は H⁰ の恒等射を誘導する。
方針：ホモトピー圏の恒等辺と関手の恒等保存を用いる。
規約：頂点は任意。使われ方：H⁰ の関手性。 -/
theorem derivedInfinityHZeroMap_id (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    derivedInfinityHZeroMap S (SSet.Truncated.Edge.id x) = 𝟙 (derivedInfinityHZero S x) :=
  (derivedInfinityHZeroFunctor S).map_id ⟨x⟩

/-- 概要：任意の一単体は両端点の H⁰ の射を誘導する。
方針：その一単体に面写像の両端点を添えて端点付き辺と読む。
規約：始点は δ₁、終点は δ₀。使われ方：端点付き辺への変換なしでの利用。 -/
def derivedInfinityHZeroSimplexMap (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋1⦌) :
    derivedInfinityHZero S ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S).δ 1 e) ⟶
      derivedInfinityHZero S ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S).δ 0 e) :=
  derivedInfinityHZeroMap S ⟨e, rfl, rfl⟩

/-- 概要：合成を表す三角形の三辺の H⁰ は実際に合成する。
方針：三角形のホモトピー圏の合成式に H⁰ 関手を適用する。
規約：合成は Mathlib の ≫ の順。使われ方：H⁰ の関手性の具体的な形。 -/
theorem derivedInfinityHZeroMap_comp {x y z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)) x y}
    {f : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)) y z}
    {g : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)) x z}
    (t : SSet.Truncated.Edge.CompStruct e f g) :
    derivedInfinityHZeroMap S e ≫ derivedInfinityHZeroMap S f = derivedInfinityHZeroMap S g := by
  exact ((derivedInfinityHZeroFunctor S).map_comp _ _).symm.trans
    (congrArg (derivedInfinityHZeroFunctor S).map t.homotopyCategory₂_fac)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
