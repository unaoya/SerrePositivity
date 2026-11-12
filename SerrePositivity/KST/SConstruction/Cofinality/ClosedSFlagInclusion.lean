module
public import SerrePositivity.KST.SConstruction.Cofinality.ClosedSFlagComparison

/-!
概要：供給側 R_P の S 交換は元の周囲の二重関手圏への包含を保つ。
方針：元の安定模型同型の逆律と S 後合成の包含公式を合成する。
規約：元の評価と元の構造射の比較に使う射の厳密等号。
使われ方：全旗方向と全 S 方向の自然性の照合。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：供給側との元の同型は同じ ambient 包含を保つ。
方針：元の逆律を包含の前で消去する。
規約：安定模型の射としての等号。
使われ方：S 後合成後の元の二重包含の回収。 -/
lemma completionClosedFlagStableIso_hom_inclusion (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : SimplexCategory) :
    (completionClosedFlagStableIso r ι f hf n).hom ≫
      completionRelativeFlagAmbientMap r ι f hf n =
        closedStableInclusion (Fibration.Relative.closedFlagStablePredicate
          (completionImageClosedPredicate r ι f hf) n) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ closedStableInclusion
      (Fibration.Relative.closedFlagStablePredicate (completionImageClosedPredicate r ι f hf) n))
        (completionClosedFlagStableIso r ι f hf n).hom_inv_id).trans (Category.id_comp _))

/-- 概要：供給側 R_P の S 交換は二重包含後に元の転置を回収する。
方針：元の S 交換の包含公式と完全な後合成の包含公式を合成する。
規約：元の全旗と全 Ar 図式の二つの方向を保持する。
使われ方：供給側の面・退化に対する自然性。 -/
lemma completionClosedSFlagIso_doubleInclusion (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory) :
    (completionClosedSFlagIso r ι f hf m n).hom ≫
        (completionRelativeFlagAmbientMap (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι) f hf n).val ≫
          (ihom (stdSimplex.obj n)).map
            (gappedSubcomplex m (((multiSEndofunctor r).obj ι).obj Y).carrier).ι =
      (gappedSubcomplex m (Fibration.Relative.closedFlagModel
        (completionImageClosedPredicate r ι f hf) n).carrier).ι ≫
          (ihom (arNerve m)).map (closedStableInclusion
            (Fibration.Relative.closedFlagStablePredicate
              (completionImageClosedPredicate r ι f hf) n)).val ≫
                (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve m) (stdSimplex.obj n)
                  (((multiSEndofunctor r).obj ι).obj Y).carrier).hom := by
  let e := completionClosedFlagStableIso r ι f hf n
  let H := ((sEndofunctor m).map e.hom).val
  let I := (completionRelativeFlagAmbientMap r ι f hf n).val
  let J := (completionRelativeFlagAmbientMap (r + 1)
    (Fin.cons (Opposite.op ⦋m⦌) ι) f hf n).val
  let U := (ihom (stdSimplex.obj n)).map
    (gappedSubcomplex m (((multiSEndofunctor r).obj ι).obj Y).carrier).ι
  let A := (gappedSubcomplex m (Fibration.Relative.closedFlagModel
    (completionImageClosedPredicate r ι f hf) n).carrier).ι
  let B := (gappedSubcomplex m (completionRelativeFlagStableModel r ι f hf n).carrier).ι
  let S := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve m) (stdSimplex.obj n)
    (((multiSEndofunctor r).obj ι).obj Y).carrier).hom
  have he : e.hom.val ≫ I = (closedStableInclusion
      (Fibration.Relative.closedFlagStablePredicate
        (completionImageClosedPredicate r ι f hf) n)).val :=
    congrArg Subtype.val (completionClosedFlagStableIso_hom_inclusion r ι f hf n)
  have hh : H ≫ B = A ≫ (ihom (arNerve m)).map e.hom.val :=
    sPostcompCofiber_ι m e.hom.val e.hom.property
  change (H ≫ completionRelativeSTranspose r ι f hf m n) ≫ J ≫ U = _
  have ht : completionRelativeSTranspose r ι f hf m n ≫ J ≫ U =
      B ≫ (ihom (arNerve m)).map I ≫ S :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun h => h ≫ U) (completionRelativeSTranspose_inclusion r ι f hf m n))).trans
        (completionRelativeSTransposeDiagram_inclusion r ι f hf m n)
  let L := (ihom (arNerve m)).map e.hom.val
  let M := (ihom (arNerve m)).map I
  let N := (ihom (arNerve m)).map (closedStableInclusion
    (Fibration.Relative.closedFlagStablePredicate (completionImageClosedPredicate r ι f hf) n)).val
  have hm : L ≫ M = N := ((ihom (arNerve m)).map_comp e.hom.val I).symm.trans
    (congrArg (fun h => (ihom (arNerve m)).map h) he)
  have hr : H ≫ (B ≫ M ≫ S) = A ≫ L ≫ M ≫ S :=
    (Category.assoc H B (M ≫ S)).symm.trans
      ((congrArg (fun h => h ≫ (M ≫ S)) hh).trans (Category.assoc A L (M ≫ S)))
  have hn : A ≫ L ≫ M ≫ S = A ≫ N ≫ S :=
    congrArg (fun h => A ≫ h)
      ((Category.assoc L M S).symm.trans (congrArg (fun h => h ≫ S) hm))
  exact (Category.assoc H (completionRelativeSTranspose r ι f hf m n) (J ≫ U)).trans
    ((congrArg (fun h => H ≫ h) ht).trans (hr.trans hn))

end SerrePositivity.KST.SConstruction.Cofinality
