module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TrianglePrismUpperSides

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantCoherentTriangle
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictCoherentNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TrianglePrismLowerSides

/-!
概要：strict な自然変換の円柱に由来する三角形の定値性。
方針：制限の等式と退化の自然性で通常の nerve を経由させる。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：strict な図式の円柱の三角形の豊穣辺は定値。
方針：制限の等式と退化の自然性で通常の nerve を経由させる。
規約：元の円柱の指定二単体を保持する。
使われ方：図式側の指定比較同型の簡約。 -/
lemma isConstantCoherentTriangle_natTrans_restriction
    {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : I ⥤ C} (η : F ⟶ G) {L : SSet.{max u v}}
    (j : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ L)
    (H : L ⊗ Δ[1] ⟶ SimplicialNerve C)
    (h : (j ▷ Δ[1]) ≫ H = (β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap η)
    (k : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋2⦌)
    (t : (Δ[1] : SSet.{max u v}) _⦋2⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsConstantCoherentTriangle (H.app (Opposite.op ⦋2⦌) (j.app (Opposite.op ⦋2⦌) k, t)) := by
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋2⦌))
    (show (((SSet.uliftFunctor.{v, u}).obj (nerve I)) ⊗ Δ[1]) _⦋2⦌ from (k, t))
  change H.app (Opposite.op ⦋2⦌) (j.app (Opposite.op ⦋2⦌) k, t) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋2⦌) _ at he
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isConstantCoherentTriangle_nerve _
/-- 概要：strict な図式の円柱の三角形の豊穣辺は定値。
方針：制限の等式と退化の自然性で通常の nerve を経由させる。
規約：元の円柱の指定二単体を保持する。
使われ方：図式側の指定比較同型の簡約。 -/
lemma isConstantCoherentTriangle_natTrans_upper
    {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : I ⥤ C} (η : F ⟶ G) {L : SSet.{max u v}}
    (j : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ L)
    (H : L ⊗ Δ[1] ⟶ SimplicialNerve C)
    (h : (j ▷ Δ[1]) ≫ H = (β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap η)
    (k : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsConstantCoherentTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleUpper H (j.app (Opposite.op ⦋1⦌) k)) := by
  have hn := ConcreteCategory.congr_hom (j.naturality (SimplexCategory.σ (0 : Fin 2)).op) k
  change j.app (Opposite.op ⦋2⦌) (((SSet.uliftFunctor.{v, u}).obj (nerve I)).σ 0 k) =
    L.σ 0 (j.app (Opposite.op ⦋1⦌) k) at hn
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleUpper
  rw [← hn]
  exact isConstantCoherentTriangle_natTrans_restriction η j H h _ _
/-- 概要：strict な図式の円柱の三角形の豊穣辺は定値。
方針：制限の等式と退化の自然性で通常の nerve を経由させる。
規約：元の円柱の指定二単体を保持する。
使われ方：図式側の指定比較同型の簡約。 -/
lemma isConstantCoherentTriangle_natTrans_lower
    {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : I ⥤ C} (η : F ⟶ G) {L : SSet.{max u v}}
    (j : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ L)
    (H : L ⊗ Δ[1] ⟶ SimplicialNerve C)
    (h : (j ▷ Δ[1]) ≫ H = (β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap η)
    (k : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsConstantCoherentTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower H (j.app (Opposite.op ⦋1⦌) k)) := by
  have hn := ConcreteCategory.congr_hom (j.naturality (SimplexCategory.σ (1 : Fin 2)).op) k
  change j.app (Opposite.op ⦋2⦌) (((SSet.uliftFunctor.{v, u}).obj (nerve I)).σ 1 k) =
    L.σ 1 (j.app (Opposite.op ⦋1⦌) k) at hn
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower
  rw [← hn]
  exact isConstantCoherentTriangle_natTrans_restriction η j H h _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
