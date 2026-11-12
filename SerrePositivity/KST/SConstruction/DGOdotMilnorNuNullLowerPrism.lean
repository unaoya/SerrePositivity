module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPrismBoundaryComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPrismFullBoundary
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryPushout
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathInnerFibration

/-!
概要：元実／絶対下二胞体と指定包含・商側面を同時に保持する実比較 prism。
方針：元全側境界を同じ内二ホーンへ制限し、既存の両端固定延長へ渡す。
規約：元両二胞体・元二短辺比較を保持。共有対角側面はこの延長から回収する。
使われ方：上二胞体と同じ対角側面で接合する下二胞体の全比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元実／絶対下二胞体と元内ホーン上の全側面を保つ実 prism が存在する。
方針：元側境界の全端点回収を同じ内ホーンの両端固定延長へ渡す。
規約：元両二胞体を固定。使われ方：元下二胞体の全比較の実構成。 -/
lemma exists_dgOdotMilnorNuNullLowerPrism :
    ∃ F : (Δ[1] ⊗ Δ[2] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1},
      ((Δ[1] : SSet.{u + 2}) ◁ (horn 2 1).ι) ≫ F =
        ((Δ[1] : SSet.{u + 2}) ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion 1 1) ≫
          dgOdotMilnorNuNullPrismTimeBoundary R d h 1 ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] : SSet.{u + 2}) ≫ F =
        SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d 1) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] : SSet.{u + 2}) ≫ F =
        SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h 1) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.prism_extend_innerHorn_with_endpoints (1 : Fin 3) (by decide) (by decide)
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion 1 1 ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary 2 : SSet.{u + 2}) ≫
        (β_ Δ[1] (boundary 2 : SSet.{u + 2})).hom ≫
          (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h 1).h = _
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _) _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding,
      (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h 1).h₀]
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion 1 1 ≫ (boundary 2).ι ≫ _ = _
    rw [← Category.assoc]
    congr 1
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion 1 1 ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary 2 : SSet.{u + 2}) ≫
        (β_ Δ[1] (boundary 2 : SSet.{u + 2})).hom ≫
          (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h 1).h = _
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _) _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding,
      (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h 1).h₁]
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion 1 1 ≫ (boundary 2).ι ≫ _ = _
    rw [← Category.assoc]
    congr 1

/-- 概要：元下二胞体の同じ両端と元二短辺比較を保つ実 prism。
方針：同じ全境界を指定した元存在証明から一つを取る。
規約：元両二胞体を固定。使われ方：下全比較と共有対角側面の回収。 -/
def dgOdotMilnorNuNullLowerPrism :
    (Δ[1] ⊗ Δ[2] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} :=
  (exists_dgOdotMilnorNuNullLowerPrism R d h).choose

/-- 概要：元下比較 prism は同じ内ホーン側面と元両二胞体を厳密回収する。
方針：同じ元存在証明の三つの制限式を使う。
規約：全単体の等号。使われ方：元全比較の指定二短辺・両端の保持。 -/
lemma dgOdotMilnorNuNullLowerPrism_restrictions :
    ((Δ[1] : SSet.{u + 2}) ◁ (horn 2 1).ι) ≫ dgOdotMilnorNuNullLowerPrism R d h =
        ((Δ[1] : SSet.{u + 2}) ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion 1 1) ≫
          dgOdotMilnorNuNullPrismTimeBoundary R d h 1 ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] : SSet.{u + 2}) ≫ dgOdotMilnorNuNullLowerPrism R d h =
        SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d 1) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] : SSet.{u + 2}) ≫ dgOdotMilnorNuNullLowerPrism R d h =
        SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h 1) :=
  (exists_dgOdotMilnorNuNullLowerPrism R d h).choose_spec

/-- 概要：元実／絶対下二胞体全体を結ぶ同じ実ホモトピー。
方針：元両端固定 prism の因子を交換して元二端点等号を使う。
規約：元両二胞体を変更しない。使われ方：元下二胞体の全関手比較。 -/
def dgOdotMilnorNuNullLowerTriangleHomotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d 1))
    (SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h 1)) where
  h := (β_ (Δ[2] : SSet.{u + 2}) Δ[1]).hom ≫ dgOdotMilnorNuNullLowerPrism R d h
  h₀ := by
    rw [← Category.assoc]
    exact (dgOdotMilnorNuNullLowerPrism_restrictions R d h).2.1
  h₁ := by
    rw [← Category.assoc]
    exact (dgOdotMilnorNuNullLowerPrism_restrictions R d h).2.2
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

end SerrePositivity.KST.SConstruction
