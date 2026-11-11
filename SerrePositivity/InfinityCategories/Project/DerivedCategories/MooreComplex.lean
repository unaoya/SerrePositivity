module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedHomModule
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MooreUniverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.InfinityCategory

/-! # 右写像空間の Moore 複体と切断 Hom

概要：実際の右 pinched 写像空間の Moore 正規化は τ≤0 Hom と複体として同型である。
方針：実際の単体的加群を N4 の線形模型へ移し、宇宙持ち上げの交換と γ1.5 の計算を使う。
規約：非負 chain 次数 n は cochain 次数 −n、零項は cycles である。
使われ方：D(S) の写像空間と古典的な Hom 複体の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded AlgebraicTopology
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory S D]

/-- 概要：N4 の線形単体的 Hom の Moore 複体は切断 Hom 複体である。
方針：標準座標への符号変換と γ1.5 の標準正規化同型を合成する。
規約：零項は smart truncation。使われ方：実際の pinched Hom の計算の小さい模型。 -/
def homModuleMooreIso (x y : D) :
    (normalizedMooreComplex (ModuleCat.{u} S)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := S) x y) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex (R := S) x y :=
  (normalizedMooreComplex (ModuleCat.{u} S)).mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModuleIso (R := S) x y) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := S) x y

/-- 概要：実際の右 pinched Hom の Moore 正規化は切断 Hom の宇宙持ち上げと同型である。
方針：実際の線形化の同型、正規化の宇宙交換、小さい Hom の正規化を合成する。
規約：全ての微分と可換な複体の同型。使われ方：D10 の写像空間の Moore 複体の同定。 -/
def pinchedHomMooreIso (x y : D) :
    (normalizedMooreComplex (ModuleCat.{max u v} S)).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule x y) ≅
      ((ModuleCat.uliftFunctor.{v} S).mapHomologicalComplex (.down ℕ)).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex (R := S) x y) :=
  (normalizedMooreComplex (ModuleCat.{max u v} S)).mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleCoordinateIso x y) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreUliftIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := S) x y) ≪≫
      ((ModuleCat.uliftFunctor.{v} S).mapHomologicalComplex (.down ℕ)).mapIso
        (homModuleMooreIso x y)

/-- 概要：D(S) の二頂点の実際の右写像空間の正規化 Moore 複体。
方針：頂点の semifree 複体の pinched Hom を線形化して Mathlib の正規化を適用する。
規約：各項の台は実際の右 pinched 単体。使われ方：導来写像空間の chain 模型。 -/
def derivedInfinityMooreComplex (x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    ChainComplex (ModuleCat.{u + 1} S) ℕ :=
  (normalizedMooreComplex (ModuleCat.{u + 1} S)).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (x.obj 0) (y.obj 0))

/-- 概要：D(S) の右写像空間の Moore 複体は semifree Hom の非正切断である。
方針：任意 dg 圏の pinched Hom の複体同型を Semifree(S) に適用する。
規約：有界性・完全性・環の追加仮定は不要。使われ方：導来 Hom と写像空間の同定。 -/
def derivedInfinityMooreIso (x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    derivedInfinityMooreComplex x y ≅
      ((ModuleCat.uliftFunctor.{u + 1} S).mapHomologicalComplex (.down ℕ)).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex (R := S) (x.obj 0) (y.obj 0)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMooreIso (x.obj 0) (y.obj 0)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
