module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.FixedQuillenFrameInvariance

/-!
概要：一般モデル圏の fibrant 終域の弱比較も、固定 Quillen 類で frame Hom のホモトピー同値。
方針：境界持ち上げで trivial Kan 射を得て、元の fibrant Brown 分解の二対三則を使う。
規約：SSet のモデル構造を仮定しない。使われ方：右導来像と終域置換の比較の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits HomotopicalAlgebra SSet
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [ModelCategory C]
  (A : SimplexCategory ⥤ C)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))

include hA in
/-- 元の frame Hom はモデル圏の trivial fibration を固定 Quillen 類の trivial Kan 射へ写す。 -/
lemma frameHom_trivialKanFibration {Y Z : C} (p : Y ⟶ Z) [Fibration p] [WeakEquivalence p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).mpr
  intro n
  exact boundary_lifting_of_reedyCofibrant A n hA p

include hA in
/-- fibrant 終域の弱同値は、同じ frame Hom の元の写像で実際のホモトピー同値を与える。 -/
lemma frameHom_target_homotopyEquivalence
    (hcA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    {Y Z : C} [IsFibrant Y] [IsFibrant Z] (f : Y ⟶ Z) [WeakEquivalence f] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map f) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A
  let h := Classical.choice (inferInstance : Nonempty (FibrantBrownFactorization f))
  have : Fibration h.p := (fibration_iff _).mpr h.hp
  have : IsFibrant h.Z := isFibrant_of_fibration h.p
  have : KanComplex (F.obj Y) := cosimplicialHom_kanComplex A hA hcA Y
  have : KanComplex (F.obj Z) := cosimplicialHom_kanComplex A hA hcA Z
  have : KanComplex (F.obj h.Z) := cosimplicialHom_kanComplex A hA hcA h.Z
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (F.map h.p) := frameHom_trivialKanFibration A hA h.p
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (F.map h.r) := frameHom_trivialKanFibration A hA h.r
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (F.map h.p)).isSimplicialHomotopyEquivalence
  have hr := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (F.map h.r)).isSimplicialHomotopyEquivalence
  have he : F.map h.i ≫ F.map h.r = 𝟙 _ := by
    rw [← F.map_comp, h.i_r, F.map_id]
  have hi := hr.cancel_right (he.symm ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_id _)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (F.map f)
  rw [← h.fac, F.map_comp]
  exact hi.comp hp

end
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
