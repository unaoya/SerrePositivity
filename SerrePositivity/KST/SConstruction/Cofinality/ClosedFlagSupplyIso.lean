module
public import SerrePositivity.KST.SConstruction.Cofinality.ClosedFlagSupplyComparison

/-!
概要：本質像を代入した K-B2-S1 の R_P と元の全相対旗を同型にする。
方針：一致する頂点条件の全部分圏の間で元の包含を持ち上げる。
規約：全自然変換と元の ambient 包含を保持する。
使われ方：相対 fiber 供給の右項と元の相対旗の接続。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：供給側 R_P から元の相対旗への包含を保つ射。
方針：同じ旗の元の周囲の関手を一致する条件で持ち上げる。
規約：元の全高次単体を保持する。
使われ方：fiber 右項の同じ実現への比較の順射。 -/
def completionClosedFlagToRelative (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : SimplexCategory) :
    (Fibration.Relative.closedFlagModel (completionImageClosedPredicate r ι f hf) n).carrier ⟶
      suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf (stdSimplex.obj n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift
    (multiRelativeFlagPredicate r ι Y
      (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex (stdSimplex.obj n))
    (closedStableInclusion (Fibration.Relative.closedFlagStablePredicate
      (completionImageClosedPredicate r ι f hf) n)).val (by
        intro v
        exact (completionClosedFlagPredicate_iff r ι f hf n v.val).mp
          (closedSubcategory_vertex _ v))

/-- 概要：元の相対旗から供給側 R_P への包含を保つ射。
方針：元の全体持ち上げの条件を供給側の閉じた条件へ移す。
規約：元の ambient 関手を保つ。
使われ方：fiber 右項の比較の逆射。 -/
def completionRelativeFlagToClosed (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : SimplexCategory) :
    suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf (stdSimplex.obj n) ⟶
      (Fibration.Relative.closedFlagModel (completionImageClosedPredicate r ι f hf) n).carrier :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (Fibration.Relative.closedFlagStablePredicate
    (completionImageClosedPredicate r ι f hf) n).predicate
    (multiRelativeFlagsInclusion r ι Y
      (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex (stdSimplex.obj n)) (by
        intro v
        exact (completionClosedFlagPredicate_iff r ι f hf n v.val).mpr
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v))

/-- 概要：同じ本質像の供給側 R_P と元の相対旗の厳密な同型。
方針：包含を保つ二つの持ち上げの往復を部分型の等号で確認する。
規約：全高次の ambient 射を保持する。
使われ方：相対 fiber の R_P の未置換比較。 -/
def completionClosedFlagIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : SimplexCategory) :
    (Fibration.Relative.closedFlagModel (completionImageClosedPredicate r ι f hf) n).carrier ≅
      suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf (stdSimplex.obj n) where
  hom := completionClosedFlagToRelative r ι f hf n
  inv := completionRelativeFlagToClosed r ι f hf n
  hom_inv_id := by
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    rfl

end SerrePositivity.KST.SConstruction.Cofinality
