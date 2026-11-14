module
public import SerrePositivity.KST.Fibration.CofiberFamilyTranspose

/-! # W 列の共通 cofiber 補完を関手圏の実列として保持

元の列の普遍評価と、全合成辺の補完の底辺を関手圏で厳密に照合する。
これを関手圏内の八面体の入力にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- W 列図式圏全体をパラメーターとする元の普遍評価。 -/
def weakStringUniversalFamily {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) : stdSimplex.obj n ⟶ (ihom (weakStringCategory q n)).obj B.obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (weakStringCategory q n) (stdSimplex.obj n) B.obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q n)).ι

/-- 共通補完を全 cofiber 四角形の実際の族へ含める。 -/
def weakStringCofiberFamilyInput {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) : weakStringCategory q n ⟶ cofiberDiagrams B.obj :=
  (weakStringCofiberExact q α).val ≫
    (relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).val

/-- 全四角形の族の射影も、元の全合成辺の制限を厳密に回収する。 -/
lemma weakStringCofiberFamilyInput_projection {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    weakStringCofiberFamilyInput q α ≫ cofiberProjection B.obj =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q n)).ι ≫
        (pre (stdSimplex.map α)).app B.obj := by
  let ι := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι
  calc
    _ = (weakStringCofiberExact q α).val ≫ (weakCofiberProjection q ≫ ι) :=
      (Category.assoc _ _ _).trans
        (congrArg ((weakStringCofiberExact q α).val ≫ ·) (weakCofiberProjection_ι q).symm)
    _ = (weakStringEdgeExact q α).val ≫ ι :=
      congrArg (fun f : weakStringModel q n ⟶ weakArrowModel q => f.val ≫ ι)
        (weakStringCofiberExact_projection q α)
    _ = _ := weakStringEdgeMap_ι q α

/-- 共通補完の全高次族を、元の列図式圏上の実 cofiber 列として保持する。 -/
def weakStringCofiberFamily {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle ((ihom (weakStringCategory q n)).obj B.obj) :=
  cofiberFamilyZeroTriangle (weakStringCofiberFamilyInput q α)

/-- 族の実列は関手圏の cofiber 列である。 -/
lemma weakStringCofiberFamily_isCofiber {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence (weakStringCofiberFamily q α) :=
  cofiberFamily_isCofiber (weakStringCofiberFamilyInput q α)

/-- 関手圏の列の底辺は、元の普遍評価の指定した実合成辺そのもの。 -/
lemma weakStringCofiberFamily_bottom {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (weakStringCofiberFamily q α).square =
      stdSimplex.map α ≫ weakStringUniversalFamily q n := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ cofiberFamilySquare (weakStringCofiberFamilyInput q α) = _
  rw [cofiberFamilySquare_bottom, weakStringCofiberFamilyInput_projection]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app _ _

/-- 共通の全四角形の族も、元の列の再添字と厳密に可換する。 -/
lemma weakStringCofiberFamilyInput_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) (α : ⦋1⦌ ⟶ m) :
    weakStringMap q θ ≫ weakStringCofiberFamilyInput q α =
      weakStringCofiberFamilyInput q (α ≫ θ) := by
  exact congrArg (fun f : weakStringModel q n ⟶ weakCofiberModel q =>
    f.val ≫ (relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).val) (weakStringCofiberExact_reindex q θ α)

/-- 関手圏の cofiber 族を引き戻すと、同じ合成辺の共通補完を厳密に回収する。 -/
lemma weakStringCofiberFamily_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) (α : ⦋1⦌ ⟶ m) :
    (weakStringCofiberFamily q α).square ≫ (pre (weakStringMap q θ)).app B.obj =
      (weakStringCofiberFamily q (α ≫ θ)).square := by
  change cofiberFamilySquare (weakStringCofiberFamilyInput q α) ≫
    (pre (weakStringMap q θ)).app B.obj = _
  rw [cofiberFamilySquare, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre]
  change cofiberFamilySquare (weakStringMap q θ ≫ weakStringCofiberFamilyInput q α) = _
  rw [weakStringCofiberFamilyInput_reindex]
  rfl

/-- 関手圏内の cofiber 頂点は、既存の完全な核値 cofiber 関手を厳密に回収する。 -/
lemma weakStringCofiberFamily_quotient {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (weakStringCofiberFamily q α).square 1 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((weakStringKernelCofiber q α).val ≫
        (closedStableInclusion (kernelClosedPredicate q)).val) := by
  change (cofiberFamilySquare (weakStringCofiberFamilyInput q α)).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) = _
  rw [cofiberFamilySquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
  change ((weakStringCofiberExact q α).val ≫
    (relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).val) ≫ (cofiberStableQuotient (sInputModel B)).val =
    ((weakStringCofiberExact q α).val ≫
      (relativeCofiberQuotient (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q)).val) ≫ (closedStableInclusion (kernelClosedPredicate q)).val
  rw [Category.assoc, Category.assoc]
  exact congrArg ((weakStringCofiberExact q α).val ≫ ·)
    (congrArg Subtype.val (relativeCofiberQuotient_inclusion
      (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q))).symm

/-- 同じ cofiber 頂点の商像は、関手圏の実際の零対象である。 -/
lemma weakStringCofiberFamily_kernel {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((ihom (weakStringCategory q n)).map q.hom).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (weakStringCofiberFamily q α).square 1 1)) := by
  rw [weakStringCofiberFamily_quotient]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (((weakStringKernelCofiber q α).val ≫
    (closedStableInclusion (kernelClosedPredicate q)).val) ≫ q.hom))
  apply isZeroVertex_functorVertex_of_pointwise
  intro v
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
    ((weakStringKernelCofiber q α).val.app (Opposite.op ⦋0⦌) v)

end SerrePositivity.KST.Fibration
