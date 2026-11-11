module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SecondTriangleCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FirstTriangleCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.NestedCutFixedTarget
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.StrictDiagramMappingNaturality

/-!
概要：元の零成分と終域輸送から、第二三角形の同じ標準合成図式を定める。
方針：時間 0,0,1 と 0,1,1 の二重切断を使う。
規約：元の全 Hom の各単体をパラメーターとして保つ。
使われ方：元の第二三角形全体と標準合成三角形の厳密な一致。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 第二三角形の内側零頂点は、外側切断で保持される。 -/
lemma cocartesianSecondTriangleTime_support {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) :
    ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime a i = 0 → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime a i = 0 := by
  intro i hi
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_apply] at hi
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime_apply]
  generalize (stdSimplex.objEquiv a) i = k at *
  fin_cases k
  · rfl
  · exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hi)
  · exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hi)

variable (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) {n : ℕ}
variable (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 0)
local notation "B" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 0)
local notation "Z" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 1)
local notation "f₀₁" => (CategoryTheory.Functor.map G.val _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow : B ⟶ Z)
local notation "s₀" => NatTrans.app
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F.val G.val (ULift.up 0)))
  (Opposite.op ⦋n⦌) s

/-- 元の可変零成分と終域輸送を使った、同じ第二三角形の標準合成切断図式。 -/
def cocartesianSecondTriangleCanonicalSimplex : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (X := A) (Y := B) s₀
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' B Z f₀₁) n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime a) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime a)

/-- 同じ標準第二三角形の最初の対象は、元の始域図式の零成分。 -/
lemma cocartesianSecondTriangleCanonicalSimplex_obj_zero
    (i : Fin (n + 1)) (hi : (stdSimplex.objEquiv a) i = 0) :
    (cocartesianSecondTriangleCanonicalSimplex F G a s).obj ⟨ULift.up i⟩ = A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex_obj_zero _ _ _ _ (cocartesianSecondTriangleTime_support a)
    i (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_zero a i hi)

/-- 同じ標準第二三角形の中間対象は、元の終域図式の零成分。 -/
lemma cocartesianSecondTriangleCanonicalSimplex_obj_middle
    (i : Fin (n + 1)) (hi : (stdSimplex.objEquiv a) i = 1) :
    (cocartesianSecondTriangleCanonicalSimplex F G a s).obj ⟨ULift.up i⟩ = B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex_obj_middle _ _ _ _ i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime_zero a i 1 hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_one a i 0 hi)

/-- 同じ標準第二三角形の最終対象は、元の終域図式の一成分。 -/
lemma cocartesianSecondTriangleCanonicalSimplex_obj_last
    (i : Fin (n + 1)) (hi : (stdSimplex.objEquiv a) i = 2) :
    (cocartesianSecondTriangleCanonicalSimplex F G a s).obj ⟨ULift.up i⟩ = Z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex_obj_last _ _ _ _ i (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime_one a i hi)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
