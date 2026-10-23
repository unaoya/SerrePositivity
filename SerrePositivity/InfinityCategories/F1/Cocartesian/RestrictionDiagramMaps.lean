module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.NativeRestrictionMap
public import SerrePositivity.InfinityCategories.F1.Universe.OverFunctor
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramColimitCone

/-!
概要：元の native 制限と分類先の制限は、同じ反変図式の射そのもの。
方針：一般の底上の射のまま、関手の map の表示を揃える。
規約：制限写像を変更しない。
使われ方：大きい具体的な境界比較の可換式を小さい等式で照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の native 制限は、同じ core の反変図式を持ち上げた射。 -/
lemma cocartesianPullbackNativeLiftPre_eq_diagramMap {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
    {a b : Over B} (f : a ⟶ b) :
    cocartesianPullbackNativeLiftPre p q f =
      ((cocartesianPullbackNativeCoreFunctor p q) ⋙ SSet.uliftFunctor.{u + 1, u}).map f.op := rfl

/-- 持ち上げた同じ底上の射による分類先の制限も、同じ反変図式の射。 -/
lemma intervalDiagramOverPre_ulift_eq_diagramMap {B : SSet.{u}} {X : SSet.{u + 1}}
    (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X) {a b : Over B} (f : a ⟶ b) :
    intervalDiagramOverPre P Q (uliftOverMorphism f) =
      ((uliftOverFunctor B).op ⋙ intervalDiagramOverFunctor P Q).map f.op := rfl

end SerrePositivity.InfinityCategories
