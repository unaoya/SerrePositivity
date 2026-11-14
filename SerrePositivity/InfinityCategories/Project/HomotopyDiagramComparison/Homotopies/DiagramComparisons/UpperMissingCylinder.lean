module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HollowCylinder
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：上面を欠く空洞柱の anodyne 性・Kan 延長と、上面の trivial Kan 持ち上げ。
方針：Λ[1,0] と単射の pushout-product を使い、二つの未知写像を順に構成する。
規約：与えた境界・空洞写像と可換条件を保持。使われ方：HTT 5.2.4.6 の外側ホーン。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra SSet

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {Q : SSet.{u}}

/-- 既知の境界柱と下面からなり、上面を欠く部分単体集合。 -/
def upperMissingCylinder (A : Q.Subcomplex) : (Q ⊗ Δ[1]).Subcomplex :=
  A.unionProd Λ[1, (0 : Fin 2)]

/-- Λ[1,0] の pushout-product により、同じ空洞柱の包含は anodyne。 -/
lemma upperMissingCylinder_anodyne (A : Q.Subcomplex) :
    SSet.anodyneExtensions (upperMissingCylinder A).ι :=
  SSet.anodyneExtensions_unionProd_ι A _ (SSet.anodyneExtensions.horn_ι _)

/-- 既知の空洞柱上の写像を、そのまま保持して Kan 複体内へ延長する。 -/
lemma upperMissingCylinder_extension (A : Q.Subcomplex) {X : SSet.{u}} [KanComplex X]
    (f : (upperMissingCylinder A : SSet) ⟶ X) :
    ∃ g : Q ⊗ Δ[1] ⟶ X, (upperMissingCylinder A).ι ≫ g = f := by
  have : HasLiftingProperty (upperMissingCylinder A).ι (terminal.from X) :=
    upperMissingCylinder_anodyne A _ (by rwa [← fibration_iff])
  let sq : CommSq f (upperMissingCylinder A).ι (terminal.from X) (terminal.from _) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 上面の境界を、既知の空洞柱へ含める元の射。 -/
def upperMissingCylinderTopBoundary (A : Q.Subcomplex) :
    (A : SSet) ⟶ upperMissingCylinder A :=
  SSet.ι₁ ≫ Subcomplex.unionProd.ι₂ A (horn 1 0)

/-- 上面境界の包含は、全柱内の同じ上面の境界に一致する。 -/
lemma upperMissingCylinderTopBoundary_ι (A : Q.Subcomplex) :
    upperMissingCylinderTopBoundary A ≫ (upperMissingCylinder A).ι = A.ι ≫ SSet.ι₁ := by
  change (SSet.ι₁ ≫ Subcomplex.unionProd.ι₂ A (horn 1 0)) ≫
    (A.unionProd (horn 1 0)).ι = _
  rw [Category.assoc, Subcomplex.unionProd.ι₂_ι]
  exact SSet.ι₁_comp A.ι

/-- 空洞の Kan 延長後、上面を trivial Kan 射に沿って境界固定で持ち上げる。 -/
lemma upperMissingCylinder_twoStageLift (A : Q.Subcomplex) {X Y : SSet.{u}}
    [KanComplex Y] (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (f : (A : SSet) ⟶ X) (H₀ : (upperMissingCylinder A : SSet) ⟶ Y)
    (h : f ≫ p = upperMissingCylinderTopBoundary A ≫ H₀) :
    ∃ (H : Q ⊗ Δ[1] ⟶ Y) (l : Q ⟶ X),
      (upperMissingCylinder A).ι ≫ H = H₀ ∧ A.ι ≫ l = f ∧ l ≫ p = SSet.ι₁ ≫ H := by
  obtain ⟨H, hH⟩ := upperMissingCylinder_extension A H₀
  have hp : f ≫ p = A.ι ≫ (SSet.ι₁ ≫ H) := by
    calc
      f ≫ p = upperMissingCylinderTopBoundary A ≫ H₀ := h
      _ = (upperMissingCylinderTopBoundary A ≫ (upperMissingCylinder A).ι) ≫ H := by
        rw [Category.assoc, hH]
      _ = (A.ι ≫ SSet.ι₁) ≫ H := by rw [upperMissingCylinderTopBoundary_ι]
      _ = _ := Category.assoc _ _ _
  have : HasLiftingProperty A.ι p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem _ inferInstance
  let sq : CommSq f A.ι p (SSet.ι₁ ≫ H) := ⟨hp⟩
  exact ⟨H, sq.lift, hH, sq.fac_left, sq.fac_right⟩

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
