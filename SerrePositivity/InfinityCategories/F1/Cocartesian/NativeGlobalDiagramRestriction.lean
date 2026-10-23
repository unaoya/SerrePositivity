module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.HornBoundaryDiagramPullbacks

/-!
概要：元の全 native Hom の大域制限を、同じ反変図式の値へ端点を揃えて写す。
方針：一般の底上の対象のまま端点を正規化し、元の厳密な自然性を移す。
規約：元の全 Hom と同じ制限写像を保持する。
使われ方：境界比較の大域 Hom への前合成と両射影の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]

/-- 元の大域 native 制限を、同じ反変図式の端点へ揃えた射。 -/
def cocartesianNativeGlobalDiagramRestriction (a : Over B) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (quasicategoryCore (cocartesianRelativeFunctorSpace p q) : SSet.{u}) ⟶
    (cocartesianPullbackNativeLiftCoreFunctor p q).obj (Opposite.op a) :=
  cocartesianPullbackNativeLiftRestriction p q a

/-- 同じ端点表示の射は、元の制限そのもの。 -/
lemma cocartesianNativeGlobalDiagramRestriction_eq (a : Over B) :
    cocartesianNativeGlobalDiagramRestriction p q a =
      cocartesianPullbackNativeLiftRestriction p q a := rfl

/-- 同じ端点表示でも、大域制限は底上の射に厳密に自然。 -/
lemma cocartesianNativeGlobalDiagramRestriction_naturality {a b : Over B} (f : a ⟶ b) :
    cocartesianNativeGlobalDiagramRestriction p q b ≫
      (cocartesianPullbackNativeLiftCoreFunctor p q).map f.op =
    cocartesianNativeGlobalDiagramRestriction p q a := by
  have h := cocartesianPullbackNativeLiftRestriction_naturality p q f
  simp only [cocartesianPullbackNativeLiftPre_eq_diagramMap] at h
  dsimp only [cocartesianNativeGlobalDiagramRestriction,
    cocartesianPullbackNativeLiftCoreFunctor, Functor.comp_obj, Functor.comp_map,
    cocartesianPullbackNativeCoreFunctor, cocartesianPullbackNativeFunctor,
    quasicategoryCoreFunctor] at h ⊢
  exact h

/-- 分類先の大域制限も、同じ反変図式の端点へ揃えて表示する。 -/
def intervalDiagramGlobalDiagramRestriction {B₀ : SSet.{u}} {X : SSet.{u + 1}}
    (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B₀ ⟶ X) (a : Over B₀) :
    intervalMappingSpace (functorVertex P) (functorVertex Q) ⟶
      (intervalDiagramLiftOverFunctor P Q).obj (Opposite.op a) :=
  intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map a.hom) P Q

/-- 同じ分類先の大域制限も、底上の射に厳密に自然。 -/
lemma intervalDiagramGlobalDiagramRestriction_naturality {B₀ : SSet.{u}} {X : SSet.{u + 1}}
    (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B₀ ⟶ X) {a b : Over B₀} (f : a ⟶ b) :
    intervalDiagramGlobalDiagramRestriction P Q b ≫
      (intervalDiagramLiftOverFunctor P Q).map f.op =
    intervalDiagramGlobalDiagramRestriction P Q a := by
  have h := intervalDiagramOverPre_restriction P Q (uliftOverMorphism f)
  simp only [intervalDiagramOverPre_ulift_eq_diagramMap] at h
  dsimp only [intervalDiagramGlobalDiagramRestriction, intervalDiagramLiftOverFunctor]
  exact h

end SerrePositivity.InfinityCategories
