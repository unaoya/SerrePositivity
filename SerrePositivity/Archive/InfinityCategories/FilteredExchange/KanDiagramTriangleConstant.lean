module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantCoherentTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeDiagramEdges
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictCoherentNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TrianglePrismLowerSides

/-!
概要：strict な自然変換の円柱に由来する三角形の定値性。
方針：制限の等式と退化の自然性で通常の nerve を経由させる。
規約：指定された三角形と同型の値を保持する。
使われ方：Kan 錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：strict な図式の円柱の三角形の豊穣辺は定値。
方針：制限の等式と退化の自然性で通常の nerve を経由させる。
規約：元の円柱の指定二単体を保持する。
使われ方：図式側の指定比較同型の簡約。 -/
lemma isConstantCoherentTriangle_kanDiagram_restriction
    {I : Type u} [SmallCategory I] (F : I ⥤ KanObject.{u}) {L : SSet.{u + 1}}
    (j : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ L)
    (H : L ⊗ Δ[1] ⟶ SpaceInfinity.{u})
    (h : (j ▷ Δ[1]) ≫ H = CartesianMonoidalCategory.fst _ _ ≫ kanDiagramCoherentNerve F)
    (k : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋2⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋2⦌) :
    IsConstantCoherentTriangle (H.app (Opposite.op ⦋2⦌) (j.app (Opposite.op ⦋2⦌) k, t)) := by
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋2⦌))
    (show (((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) ⊗ Δ[1]) _⦋2⦌ from (k, t))
  change H.app (Opposite.op ⦋2⦌) (j.app (Opposite.op ⦋2⦌) k, t) =
    (nerveToCoherent KanObject.{u}).app (Opposite.op ⦋2⦌) _ at he
  rw [he]
  exact isConstantCoherentTriangle_nerve _
/-- 概要：strict な図式の円柱の三角形の豊穣辺は定値。
方針：制限の等式と退化の自然性で通常の nerve を経由させる。
規約：元の円柱の指定二単体を保持する。
使われ方：図式側の指定比較同型の簡約。 -/
lemma isConstantCoherentTriangle_kanDiagram_upper
    {I : Type u} [SmallCategory I] (F : I ⥤ KanObject.{u}) {L : SSet.{u + 1}}
    (j : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ L)
    (H : L ⊗ Δ[1] ⟶ SpaceInfinity.{u})
    (h : (j ▷ Δ[1]) ≫ H = CartesianMonoidalCategory.fst _ _ ≫ kanDiagramCoherentNerve F)
    (k : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋1⦌) :
    IsConstantCoherentTriangle (homotopyEdgeTriangleUpper H (j.app (Opposite.op ⦋1⦌) k)) := by
  have hn := ConcreteCategory.congr_hom (j.naturality (SimplexCategory.σ (0 : Fin 2)).op) k
  change j.app (Opposite.op ⦋2⦌) (((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)).σ 0 k) =
    L.σ 0 (j.app (Opposite.op ⦋1⦌) k) at hn
  unfold homotopyEdgeTriangleUpper
  rw [← hn]
  exact isConstantCoherentTriangle_kanDiagram_restriction F j H h _ _
/-- 概要：strict な図式の円柱の三角形の豊穣辺は定値。
方針：制限の等式と退化の自然性で通常の nerve を経由させる。
規約：元の円柱の指定二単体を保持する。
使われ方：図式側の指定比較同型の簡約。 -/
lemma isConstantCoherentTriangle_kanDiagram_lower
    {I : Type u} [SmallCategory I] (F : I ⥤ KanObject.{u}) {L : SSet.{u + 1}}
    (j : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ L)
    (H : L ⊗ Δ[1] ⟶ SpaceInfinity.{u})
    (h : (j ▷ Δ[1]) ≫ H = CartesianMonoidalCategory.fst _ _ ≫ kanDiagramCoherentNerve F)
    (k : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋1⦌) :
    IsConstantCoherentTriangle (homotopyEdgeTriangleLower H (j.app (Opposite.op ⦋1⦌) k)) := by
  have hn := ConcreteCategory.congr_hom (j.naturality (SimplexCategory.σ (1 : Fin 2)).op) k
  change j.app (Opposite.op ⦋2⦌) (((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)).σ 1 k) =
    L.σ 1 (j.app (Opposite.op ⦋1⦌) k) at hn
  unfold homotopyEdgeTriangleLower
  rw [← hn]
  exact isConstantCoherentTriangle_kanDiagram_restriction F j H h _ _

end SerrePositivity.InfinityCategories.F2
