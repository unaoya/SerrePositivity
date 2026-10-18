module

public import SerrePositivity.KST.DerivedGeometry.SheafAcyclicTria
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
概要：層の acyclic dg 商の H⁰ を元の層の Mathlib 導来圏と比較する。
方針：acyclic 部分圏の同定から trW を同定し、既存の導来局所化の同値を使う。
規約：半自由分解・K-flat 性・H⁰ の代表可能性は全て証明済みのものを使う。
使われ方：Drinfeld Lemma 13.5・Thm 3.4・§3.5、KST D4・§10-7、Toën §3.2。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits AlgebraicGeometry
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：層の tria の acyclic 商の弱同値は Mathlib の acyclic 商の弱同値の逆像。
方針：三角部分圏の一致と、三角同値による cone の比較を使う。
規約：対象条件の一致だけで局所化の比較を済ませない。
使われ方：Drinfeld Thm 3.4、KST D4 の導来局所化。
-/
theorem acyclicTrW_eq :
    (triaImage CoefficientDGBase.{u} B.Complexes B.acyclicComplexes).trW =
      (_root_.HomotopyCategory.subcategoryAcyclic B.Modules).trW.inverseImage
        B.triaHomotopyEquivalence.functor := by
  rw [B.acyclicTriaImage_eq]
  ext K L f
  change (( _root_.HomotopyCategory.subcategoryAcyclic B.Modules).inverseImage
    B.triaHomotopyEquivalence.functor).trW f ↔ _
  rw [ObjectProperty.inverseImage_trW_iff]
  rfl

/--
概要：tria と元の層ホモトピー圏の比較を局所化の射として束ねる。
方針：証明した trW の逆像の等式を既存 LocalizerMorphism に渡す。
規約：新しい局所化の構成を追加しない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4 の導来比較の正方形。
-/
def derivedComparisonLocalizer :
    LocalizerMorphism (triaImage CoefficientDGBase.{u} B.Complexes B.acyclicComplexes).trW
      (_root_.HomotopyCategory.subcategoryAcyclic B.Modules).trW :=
  LocalizerMorphism.ofEq B.acyclicTrW_eq

/--
概要：層の tria の acyclic 局所化から元の層の局所化への関手は同値になる。
方針：元の比較の圏同値と trW の正確な対応を使う。
規約：同値性を未証明のフィールドとして仮定しない。
使われ方：Drinfeld Thm 3.4、KST D4 の Mathlib 導来圏への比較。
-/
instance derivedComparisonLocalizer_isLocalizedEquivalence :
    B.derivedComparisonLocalizer.IsLocalizedEquivalence := by
  let : B.derivedComparisonLocalizer.functor.IsEquivalence :=
    B.triaHomotopyEquivalence.isEquivalence_functor
  apply LocalizerMorphism.IsLocalizedEquivalence.of_equivalence
  change (_root_.HomotopyCategory.subcategoryAcyclic B.Modules).trW ≤
    (triaImage CoefficientDGBase.{u} B.Complexes B.acyclicComplexes).trW.map
      B.triaHomotopyEquivalence.functor
  rw [B.acyclicTrW_eq, MorphismProperty.map_inverseImage_eq_of_isEquivalence]

variable [HasDerivedCategory.{w} B.Modules]

/--
概要：元の tria の指定 acyclic Verdier 商と Mathlib の層導来圏の同値。
方針：証明済みの局所化同値を Mathlib の実際の Qh に適用する。
規約：選ばれた Mathlib 導来圏を保持し、冪等完備化を加えない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4・§10-7、Toën §3.2。
-/
def triaDerivedEquivalence :
    TriaQuotient CoefficientDGBase.{u} B.Complexes B.acyclicComplexes ≌
      _root_.DerivedCategory B.Modules :=
  (B.derivedComparisonLocalizer.localizedFunctor
    (triaQuotient CoefficientDGBase.{u} B.Complexes B.acyclicComplexes)
    (_root_.DerivedCategory.Qh : _root_.HomotopyCategory B.Modules (.up ℤ) ⥤
      _root_.DerivedCategory B.Modules)).asEquivalence

/--
概要：tria の導来比較は同じホモトピー圏の関手と Qh の比較正方形を持つ。
方針：局所化の既存の因子分解同型を使う。
規約：元の層の導来像を読む関手を固定する。
使われ方：Drinfeld §3.5、KST D4 の Dqc への制限。
-/
def triaDerivedSquare :
    triaQuotient CoefficientDGBase.{u} B.Complexes B.acyclicComplexes ⋙
        B.triaDerivedEquivalence.functor ≅
      B.triaHomotopyEquivalence.functor ⋙ _root_.DerivedCategory.Qh :=
  Localization.Lifting.iso _ (triaImage CoefficientDGBase.{u} B.Complexes B.acyclicComplexes).trW
    (B.derivedComparisonLocalizer.functor ⋙ _root_.DerivedCategory.Qh)
    (B.derivedComparisonLocalizer.localizedFunctor
      (triaQuotient CoefficientDGBase.{u} B.Complexes B.acyclicComplexes)
      (_root_.DerivedCategory.Qh : _root_.HomotopyCategory B.Modules (.up ℤ) ⥤
        _root_.DerivedCategory B.Modules))

/--
概要：層の acyclic dg 商自体の H⁰ と Mathlib の元の層導来圏の同値。
方針：半自由分解後の商の H⁰ 比較、元の Verdier 商への移送、同じ acyclic 局所化を合成する。
規約：導来比較を仮定しない。H⁰ を tria に定義し直さない。
使われ方：Drinfeld Lemma 13.5・Thm 3.4、KST D4・§13 決定11、Toën §3.2。
-/
def derivedDGHomotopyEquivalence :
    HomotopyCategory CoefficientDGBase.{u} B.DerivedDG ≌ _root_.DerivedCategory B.Modules :=
  B.derivedDGHomotopyVerdierEquivalence.trans B.triaDerivedEquivalence

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
