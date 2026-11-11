module
public import SerrePositivity.KST.SConstruction.Cofinality.ClosedFlagSupplyIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceStability

/-!
概要：元の相対旗自体を安定模型にし、供給側 R_P との完全な同型を保持する。
方針：同じ全部分旗の厳密同型で安定性を移し、元の両射の完全性を添える。
規約：元の相対旗の全自然変換と元の包含を保持する。
使われ方：元の相対旗に S 構成を適用する接続。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：供給側 R_P との同じ元の同型は quasicategory の同値。
方針：厳密な二つの逆律を元の関手頂点の可逆二胞体へ移す。
規約：順射と逆射は元の同型の両射。
使われ方：相対旗の安定性の移送。 -/
def completionClosedFlagEquivalence (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (Fibration.Relative.closedFlagModel (completionImageClosedPredicate r ι f hf) n).carrier
      (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf (stdSimplex.obj n)) := by
  let e := completionClosedFlagIso r ι f hf n
  exact ⟨e.hom, e.inv,
    eqToIso (congrArg (fun h => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h)) e.hom_inv_id),
    eqToIso (congrArg (fun h => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h)) e.inv_hom_id)⟩

/-- 概要：元の全相対旗は安定である。
方針：同じ供給側 R_P との同値で安定性を移す。
規約：元の ambient 全自然変換を制限しない。
使われ方：相対旗の S 構成の入力。 -/
lemma completionRelativeFlags_isStable (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf (stdSimplex.obj n)) :=
  (completionClosedFlagEquivalence r ι f hf n).isStable_iff.mp inferInstance

/-- 概要：元の相対旗そのものの安定模型。
方針：元の単体集合へ検証済みの安定性を添える。
規約：fiber 供給に合わせて底の圏を置換しない。
使われ方：元の相対旗に対する S と実現の適用。 -/
def completionRelativeFlagStableModel (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : SimplexCategory) : StableModel.{u} where
  carrier := suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf (stdSimplex.obj n)
  quasicategory := inferInstance
  stable := completionRelativeFlags_isStable r ι f hf n

/-- 概要：供給側 R_P と元の相対旗は安定模型の圏でも同型。
方針：同じ厳密同型の両射の quasicategory 同値性から完全性を添える。
規約：元の包含を保つ両射を変更しない。
使われ方：相対 fiber の元の core S 実現への接続。 -/
def completionClosedFlagStableIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : SimplexCategory) :
    Fibration.Relative.closedFlagModel (completionImageClosedPredicate r ι f hf) n ≅
      completionRelativeFlagStableModel r ι f hf n where
  hom := by
    letI := completionRelativeFlags_isStable r ι f hf n
    let e := completionClosedFlagEquivalence r ι f hf n
    have hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
    exact ⟨e.hom, @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ _ e.hom hE,
      fun t ht => @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber _ _ e.hom hE t ht⟩
  inv := by
    letI := completionRelativeFlags_isStable r ι f hf n
    let e := completionClosedFlagEquivalence r ι f hf n
    have hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
    exact ⟨e.inv, @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ _ e.inv hE,
      fun t ht => @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber _ _ e.inv hE t ht⟩
  hom_inv_id := Subtype.ext (completionClosedFlagIso r ι f hf n).hom_inv_id
  inv_hom_id := Subtype.ext (completionClosedFlagIso r ι f hf n).inv_hom_id

end SerrePositivity.KST.SConstruction.Cofinality
