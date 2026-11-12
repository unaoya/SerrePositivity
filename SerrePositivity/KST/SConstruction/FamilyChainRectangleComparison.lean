module
public import SerrePositivity.KST.SConstruction.FamilyChainRectangle
public import SerrePositivity.KST.SConstruction.FamilyChainCompositeOperations
public import SerrePositivity.KST.SConstruction.FamilyCylinderClassComparison

/-! # 全交換セルの両辺路を合成した円柱の実比較
概要：長方形の二つの全辺路を実円柱に合成し、両端固定の実二次元写像で比較する。
方針：元の全正方形から証明した合成式を実比較三角形へ渡す。
規約：両側の全区間と合成三角形を保持し、異なる二列の比較を内部構成する。
使われ方：元の全交換セルと共有末尾から raw 構造適合を取り出す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {U E : SSet.{u}} {f g : U ⊗ (Δ[1] : SSet.{u}) ⟶ E}
  (c : FamilyHomotopyChain f g)

/-- 長方形の元の入口円柱を通り、一側の全境界区間を順に通る辺路。 -/
def familyChainRectangleLeft : FamilyHomotopyChain (SSet.ι₀ ≫ f) (SSet.ι₁ ≫ g) :=
  .cons (familyCylinder f) (familyHomotopyChainPrecomp (SSet.ι₁ (X := U)) c)

/-- 他側の全境界区間を順に通り、元の出口円柱を通る辺路。 -/
def familyChainRectangleRight : FamilyHomotopyChain (SSet.ι₀ ≫ f) (SSet.ι₁ ≫ g) :=
  familyHomotopyChainAppend (familyHomotopyChainPrecomp (SSet.ι₀ (X := U)) c)
    (familyHomotopyChainSingle (familyCylinder g))

/-- 一側の元の全区間をそのまま記録する。 -/
lemma familyChainRectangleLeft_trace :
    familyHomotopyChainTrace (familyChainRectangleLeft c) =
      f :: (familyHomotopyChainTrace c).map
        ((SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
  change f :: familyHomotopyChainTrace (familyHomotopyChainPrecomp _ c) = _
  rw [familyHomotopyChainPrecomp_trace]

/-- 他側の元の全区間と最後の出口を同じ順序で記録する。 -/
lemma familyChainRectangleRight_trace :
    familyHomotopyChainTrace (familyChainRectangleRight c) =
      (familyHomotopyChainTrace c).map
        ((SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ ·) ++ [g] := by
  rw [familyChainRectangleRight, familyHomotopyChainAppend_trace,
    familyHomotopyChainPrecomp_trace, familyHomotopyChainSingle_trace]
  rfl

/-- 元の全交換セルが、この異なる二つの全辺路の同じ合成を与える。 -/
lemma familyChainRectangleLeft_class_eq :
    familyChainCompositeClass (familyChainRectangleLeft c) =
      familyChainCompositeClass (familyChainRectangleRight c) := by
  change _ = familyChainCompositeClass (familyHomotopyChainAppend _ _)
  rw [familyChainCompositeClass_append, familyChainCompositeClass_single]
  exact familyChainRectangle_class c

/-- 元の各辺路の全合成証人から、両円柱の合成式を照合する。 -/
lemma familyChainRectangle_composite_class_eq [KanComplex E] :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (familyChainCompositeData (familyChainRectangleLeft c)).homotopy) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (familyChainCompositeData (familyChainRectangleRight c)).homotopy) :=
  (familyChainCompositionWitness_class
    (familyChainCompositeData (familyChainRectangleLeft c)).witness).trans
      ((familyChainRectangleLeft_class_eq c).trans
        (familyChainCompositionWitness_class
          (familyChainCompositeData (familyChainRectangleRight c)).witness).symm)

/-- 全セルから構成した、異なる二辺路の実合成円柱の端点固定二次元比較。 -/
def familyChainRectangleComparison [KanComplex E] : SSet.Homotopy
    (familyChainCompositeData (familyChainRectangleLeft c)).homotopy.h
    (familyChainCompositeData (familyChainRectangleRight c)).homotopy.h :=
  familyCylinderClassComparison _ _ (familyChainRectangle_composite_class_eq c)

/-- 比較の始点は元の入口の始点で、全比較時刻で固定する。 -/
lemma familyChainRectangleComparison_source [KanComplex E] :
    (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ (familyChainRectangleComparison c).h =
      fst U (Δ[1] : SSet.{u}) ≫ SSet.ι₀ ≫ f :=
  familyCylinderClassComparison_source _ _ _

/-- 比較の終点は元の出口の終点で、全比較時刻で固定する。 -/
lemma familyChainRectangleComparison_target [KanComplex E] :
    (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ (familyChainRectangleComparison c).h =
      fst U (Δ[1] : SSet.{u}) ≫ SSet.ι₁ ≫ g :=
  familyCylinderClassComparison_target _ _ _

end SerrePositivity.KST.SConstruction
