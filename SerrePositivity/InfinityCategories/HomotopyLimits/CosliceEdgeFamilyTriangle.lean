module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFamilyCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedBaseTerminalTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedBaseHomotopyClasses

/-!
概要：同じ終点族を持つ辺全体の二族を、元の二つの切断比較円柱を保って照合する。
方針：終点制限上で二円柱を二番目ホーンに貼り、底を固定して充填する。
規約：元の円柱の raw な射を変更しない。使われ方：左右の native 共通脚比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X T : SSet.{u}} [Quasicategory X] (e : (Δ[1] : SSet.{u}) ⟶ X)
  (y : X _⦋0⦌) (F G : T ⟶ coconeMappingSpace e y)
local notation "r" => cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y
variable (hFG : F ≫ cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y =
  G ≫ cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y)
local notation "S" => (F ≫ r) ≫ cosliceEdgeSectionFiber e y

/-- 第二円柱の終点表示だけを揃え、元の円柱の射はそのまま保持する。 -/
def cosliceEdgeFamilySecondCylinder : SSet.Homotopy G S where
  h := (cosliceEdgeFamilyCylinder e y G).homotopy.h
  h₀ := (cosliceEdgeFamilyCylinder e y G).homotopy.h₀
  h₁ := (cosliceEdgeFamilyCylinder e y G).homotopy.h₁.trans
    (congrArg (fun k ↦ k ≫ cosliceEdgeSectionFiber e y) hFG.symm)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 同じ終点族上で、選択済みの二つの円柱を二面として保持する実際の三角形。 -/
def cosliceEdgeFamilyTriangle : FixedBaseTerminalTriangle r (F ≫ r)
    (cosliceEdgeFamilyCylinder e y F).homotopy (cosliceEdgeFamilySecondCylinder e y F G hFG) := by
  have := cosliceTriangleTarget_trivialKanFibration e y
  exact fixedBaseTerminalTriangle r (F ≫ r) _ _
    (by simpa only [Category.assoc] using (cosliceEdgeFamilyCylinder e y F).target)
    (by
      change (cosliceEdgeFamilyCylinder e y G).homotopy.h ≫ r = fst T Δ[1] ≫ (F ≫ r)
      exact (cosliceEdgeFamilyCylinder e y G).target.trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k ↦ fst T (Δ[1] : SSet.{u}) ≫ k) hFG.symm)))

/-- 第一辺は、指定した二つの全辺族を同じ終点のまま結ぶ実際の円柱。 -/
def cosliceEdgeFamilyComparison : SSet.Homotopy F G :=
  fixedBaseTerminalTriangleFirst r (F ≫ r) _ _ (cosliceEdgeFamilyTriangle e y F G hFG)

/-- 全辺族の比較の間、元の終点族は全時刻で固定される。 -/
lemma cosliceEdgeFamilyComparison_target :
    (cosliceEdgeFamilyComparison e y F G hFG).h ≫ r = fst T Δ[1] ≫ F ≫ r :=
  (fixedBaseTerminalTriangleFirst_base r (F ≫ r) _ _
    (cosliceEdgeFamilyTriangle e y F G hFG))

/-- 三角形の第二辺は、元の第二族の切断比較円柱の raw な射そのもの。 -/
lemma cosliceEdgeFamilyTriangle_second :
    (T ◁ stdSimplex.δ (0 : Fin 3)) ≫ (cosliceEdgeFamilyTriangle e y F G hFG).family =
      (cosliceEdgeFamilyCylinder e y G).homotopy.h :=
  (cosliceEdgeFamilyTriangle e y F G hFG).second

/-- 第一辺と元の第二円柱の類を合成すると、元の第一円柱の類を回収する。 -/
lemma cosliceEdgeFamilyTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (cosliceEdgeFamilyComparison e y F G hFG)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (cosliceEdgeFamilySecondCylinder e y F G hFG)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (cosliceEdgeFamilyCylinder e y F).homotopy) := by
  have := coconeMappingSpace_kanComplex e y
  exact fixedBaseTerminalTriangle_homMk_comp r (F ≫ r) _ _
    (cosliceEdgeFamilyTriangle e y F G hFG)

/-- 同じ終点族を固定する別の実際の比較も、第一辺と同じ類を持つ。 -/
lemma cosliceEdgeFamilyComparison_homMk_unique (K : SSet.Homotopy F G)
    (hK : K.h ≫ r = fst T (Δ[1] : SSet.{u}) ≫ F ≫ r) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy K) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (cosliceEdgeFamilyComparison e y F G hFG)) := by
  have := coconeMappingSpace_kanComplex e y
  have := coconeMappingSpace_kanComplex (stdSimplex.δ (0 : Fin 2) ≫ e) y
  have := cosliceTriangleTarget_trivialKanFibration e y
  exact trivialKanFibration_homotopy_homMk_eq r K _
    (hK.trans (cosliceEdgeFamilyComparison_target e y F G hFG).symm)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
