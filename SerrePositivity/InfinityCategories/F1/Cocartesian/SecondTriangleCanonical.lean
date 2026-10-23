module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SecondTriangleCoordinates
public import SerrePositivity.InfinityCategories.F1.Cocartesian.FirstTriangleCoordinates
public import SerrePositivity.InfinityCategories.F1.Coherent.NestedCutFixedTarget
public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictDiagramMappingNaturality

/-!
概要：元の零成分と終域輸送から、第二三角形の同じ標準合成図式を定める。
方針：時間 0,0,1 と 0,1,1 の二重切断を使う。
規約：元の全 Hom の各単体をパラメーターとして保つ。
使われ方：元の第二三角形全体と標準合成三角形の厳密な一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 第二三角形の内側零頂点は、外側切断で保持される。 -/
lemma cocartesianSecondTriangleTime_support {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) :
    ∀ i, cocartesianSecondTriangleTime a i = 0 → cocartesianFirstTriangleTime a i = 0 := by
  intro i hi
  rw [cocartesianSecondTriangleTime_apply] at hi
  rw [cocartesianFirstTriangleTime_apply]
  generalize (stdSimplex.objEquiv a) i = k at *
  fin_cases k
  · rfl
  · exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hi)
  · exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hi)

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) {n : ℕ}
variable (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
local notation "A" => cocartesianTransportDiagramValue F (ULift.up 0)
local notation "B" => cocartesianTransportDiagramValue G (ULift.up 0)
local notation "Z" => cocartesianTransportDiagramValue G (ULift.up 1)
local notation "f₀₁" => (CategoryTheory.Functor.map G.val strictIntervalIndexArrow : B ⟶ Z)
local notation "s₀" => NatTrans.app
  (quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val (ULift.up 0)))
  (Opposite.op ⦋n⦌) s

/-- 元の可変零成分と終域輸送を使った、同じ第二三角形の標準合成切断図式。 -/
def cocartesianSecondTriangleCanonicalSimplex : CatInfinity.{u} _⦋n⦌ :=
  coherentCompositionNestedCutSimplex (C := QCat.{u}) (X := A) (Y := B) s₀
    (PinchedHom.constant (SimplicialCategory.homEquiv' B Z f₀₁) n)
    (cocartesianFirstTriangleTime a) (cocartesianSecondTriangleTime a)

/-- 同じ標準第二三角形の最初の対象は、元の始域図式の零成分。 -/
lemma cocartesianSecondTriangleCanonicalSimplex_obj_zero
    (i : Fin (n + 1)) (hi : (stdSimplex.objEquiv a) i = 0) :
    (cocartesianSecondTriangleCanonicalSimplex F G a s).obj ⟨ULift.up i⟩ = A :=
  coherentCompositionNestedCutSimplex_obj_zero _ _ _ _ (cocartesianSecondTriangleTime_support a)
    i (cocartesianSecondTriangleTime_zero a i hi)

/-- 同じ標準第二三角形の中間対象は、元の終域図式の零成分。 -/
lemma cocartesianSecondTriangleCanonicalSimplex_obj_middle
    (i : Fin (n + 1)) (hi : (stdSimplex.objEquiv a) i = 1) :
    (cocartesianSecondTriangleCanonicalSimplex F G a s).obj ⟨ULift.up i⟩ = B :=
  coherentCompositionNestedCutSimplex_obj_middle _ _ _ _ i
    (cocartesianFirstTriangleTime_zero a i 1 hi) (cocartesianSecondTriangleTime_one a i 0 hi)

/-- 同じ標準第二三角形の最終対象は、元の終域図式の一成分。 -/
lemma cocartesianSecondTriangleCanonicalSimplex_obj_last
    (i : Fin (n + 1)) (hi : (stdSimplex.objEquiv a) i = 2) :
    (cocartesianSecondTriangleCanonicalSimplex F G a s).obj ⟨ULift.up i⟩ = Z :=
  coherentCompositionNestedCutSimplex_obj_last _ _ _ _ i (cocartesianFirstTriangleTime_one a i hi)

end SerrePositivity.InfinityCategories
