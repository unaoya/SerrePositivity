module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.HZero
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.PullbackPresentation

/-! # 導来 ∞ 圏の全整数次数のホモロジー

概要：D(S) の頂点と辺に全整数次数のホモロジーを対応させ、H⁰ と整合させる。
方針：D3 の導来同値に Mathlib の各次数のホモロジー関手を合成する。
規約：微分は次数 +1。使われ方：D6 の長完全列と離散対象の判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded

open scoped _root_.Simplicial
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 概要：D(S) のホモトピー圏上の i 次ホモロジー関手。
方針：D3 の同値と導来圏の homologyFunctor を合成する。
規約：i は任意の整数。使われ方：長完全列を取る関手。 -/
def derivedInfinityHomologyFunctor (i : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S ⥤ ModuleCat.{u} S :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S).functor ⋙ DerivedCategory.homologyFunctor (ModuleCat S) i

/-- 概要：D(S) の頂点の i 次ホモロジー加群。
方針：頂点をホモトピー圏の対象として評価する。
規約：余鎖複体の整数次数。使われ方：離散性と長完全列の対象。 -/
def derivedInfinityHomology (i : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) : ModuleCat.{u} S :=
  (derivedInfinityHomologyFunctor S i).obj ⟨x⟩

/-- 概要：D(S) の辺は各次数のホモロジーの射を誘導する。
方針：辺のホモトピー類に各次数の関手を適用する。
規約：辺は二次切断の端点付き辺。使われ方：四角形の四辺のホモロジー。 -/
def derivedInfinityHomologyMap (i : ℤ) {x y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)) x y) :
    derivedInfinityHomology S i x ⟶ derivedInfinityHomology S i y :=
  (derivedInfinityHomologyFunctor S i).map (SSet.Truncated.HomotopyCategory₂.homMk e)

/-- 概要：導来圏を経由したホモロジーと複体ホモトピー圏のホモロジーは自然に同型。
方針：Mathlib の Qh のホモロジー比較を D3 の比較の前半で引き戻す。
規約：自然性は辺の代表元に依存しない。使われ方：具体的な複体との比較。 -/
def derivedInfinityHomologyComparison (i : ℤ) :
    derivedInfinityHomologyFunctor S i ≅
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S) ⋙
        HomotopyCategory.homologyFunctor (ModuleCat S) (.up ℤ) i :=
  NatIso.ofComponents (fun x =>
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat S) i).app
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).obj ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor.obj x)))
    (fun f => (DerivedCategory.homologyFunctorFactorsh (ModuleCat S) i).hom.naturality
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor.map f)))

/-- 概要：頂点のホモロジーはその semifree 複体のホモロジーと同型である。
方針：Qh とホモトピー商の二つの比較を合成する。
規約：全整数次数に同じ規約を用いる。使われ方：長完全列の具体的な表示。 -/
def derivedInfinityHomologyIso (i : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    derivedInfinityHomology S i x ≅ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S x).val.homology i :=
  (derivedInfinityHomologyComparison S i).app ⟨x⟩ ≪≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat S) (.up ℤ) i).app
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S x).val

/-- 概要：次数零のホモロジー関手は D5d の H⁰ 関手である。
方針：定義を評価する。規約：比較同型を挟まない等式。使われ方：D5d との整合性。 -/
lemma derivedInfinityHomologyFunctor_zero :
    derivedInfinityHomologyFunctor S 0 = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroFunctor S := rfl

/-- 概要：次数零の頂点の値は D5d の H⁰ と一致する。
方針：定義の評価。規約：任意の頂点。使われ方：H⁰ の型の読み替え。 -/
lemma derivedInfinityHomology_zero (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    derivedInfinityHomology S 0 x = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S x := rfl

/-- 概要：次数零の辺の射は D5d の H⁰ の射と一致する。
方針：同じホモトピー類の関手像の定義を評価する。
規約：任意の端点付き辺。使われ方：長完全列と既存 H⁰ の整合。 -/
lemma derivedInfinityHomologyMap_zero {x y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)) x y) :
    derivedInfinityHomologyMap S 0 e = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroMap S e := rfl

/-- 概要：次数零での複体との比較は D5d の比較同型に一致する。
方針：二つの標準比較の定義を評価する。
規約：任意の頂点。使われ方：既存の離散入力の H⁰ 同定をそのまま利用する。 -/
lemma derivedInfinityHomologyIso_zero (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    derivedInfinityHomologyIso S 0 x = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroIso S x := rfl

/-- 概要：ホモロジー比較は辺の鎖写像によるホモロジー射と両立する。
方針：Qh の比較とホモトピー商の比較の自然性を続けて使う。
規約：全整数次数。使われ方：指定された四辺を長完全列へ移す。 -/
lemma derivedInfinityHomologyIso_naturality (i : ℤ)
    {x y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)) x y) :
    derivedInfinityHomologyMap S i e ≫ (derivedInfinityHomologyIso S i y).hom =
      (derivedInfinityHomologyIso S i x).hom ≫ HomologicalComplex.homologyMap
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap (e.map ((SSet.truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))) i := by
  have h₁ := (derivedInfinityHomologyComparison S i).hom.naturality
    (SSet.Truncated.HomotopyCategory₂.homMk e)
  have h₂ := (HomotopyCategory.homologyFunctorFactors (ModuleCat S) (.up ℤ) i).hom.naturality
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap (e.map ((SSet.truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)))
  change derivedInfinityHomologyMap S i e ≫
    (derivedInfinityHomologyComparison S i).hom.app ⟨y⟩ = _ at h₁
  change derivedInfinityHomologyMap S i e ≫
    (derivedInfinityHomologyComparison S i).hom.app ⟨y⟩ ≫ _ = _
  rw [← Category.assoc, h₁, Category.assoc]
  exact congrArg ((derivedInfinityHomologyComparison S i).hom.app ⟨x⟩ ≫ ·) h₂

end SerrePositivity.InfinityCategories.Project.DerivedCategories
