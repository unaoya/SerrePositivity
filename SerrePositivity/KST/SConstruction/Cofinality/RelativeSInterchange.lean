module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeSInverse

/-!
概要：元の相対旗と S 構成の二方向の転置を厳密な同型にする。
方針：二重内部 Hom の単射な表示で交換の逆律へ帰着する。
規約：元の全高次単体と元の包含を保持する。
使われ方：相対 fiber 供給の右項を元の S 多次数の実現へ照合する。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の相対旗の S 転置と逆転置は厳密に互いに逆。
方針：元の二重包含の後で内部 Hom の二回交換を計算する。
規約：元の指定射と全多次数を保持する。
使われ方：相対 S 実現を交換する元の同型。 -/
def completionRelativeSInterchangeIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory) :
    (sStableModel m (completionRelativeFlagStableModel r ι f hf n)).carrier ≅
      (completionRelativeFlagStableModel (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι)
        f hf n).carrier := by
  let C := (((multiSEndofunctor r).obj ι).obj Y).carrier
  let R := (completionRelativeFlagStableModel r ι f hf n).carrier
  let I := (completionRelativeFlagAmbientMap r ι f hf n).val
  let J := (completionRelativeFlagAmbientMap (r + 1)
    (Fin.cons (Opposite.op ⦋m⦌) ι) f hf n).val
  let a := (gappedSubcomplex m R).ι ≫ (ihom (arNerve m)).map I
  let b := J ≫ (ihom (stdSimplex.obj n)).map (gappedSubcomplex m C).ι
  let F := completionRelativeSTranspose r ι f hf m n
  let G := completionRelativeSInverse r ι f hf m n
  let s := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve m) (stdSimplex.obj n) C).hom
  let t := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (stdSimplex.obj n) (arNerve m) C).hom
  have hi : Mono I := inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _
    (multiRelativeFlagPredicate r ι Y
      (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex
        (stdSimplex.obj n))).ι)
  have hj : Mono J := inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _
    (multiRelativeFlagPredicate (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι) Y
      (multiWideStageData stableWideCofinalitySupply (r + 1)
        (Fin.cons (Opposite.op ⦋m⦌) ι) f hf).subcomplex (stdSimplex.obj n))).ι)
  letI : Mono I := hi
  letI : Mono J := hj
  have hm : Mono ((ihom (arNerve m)).map I) := (ihom (arNerve m)).map_mono I
  have hk : Mono ((ihom (stdSimplex.obj n)).map (gappedSubcomplex m C).ι) :=
    (ihom (stdSimplex.obj n)).map_mono (gappedSubcomplex m C).ι
  have ha : Mono a := mono_comp' (inferInstanceAs (Mono (gappedSubcomplex m R).ι)) hm
  have hb : Mono b := mono_comp' hj hk
  letI : Mono a := ha
  letI : Mono b := hb
  have hF : F ≫ b = a ≫ s :=
    (Category.assoc F J ((ihom (stdSimplex.obj n)).map (gappedSubcomplex m C).ι)).symm.trans
      ((congrArg (fun h => h ≫ (ihom (stdSimplex.obj n)).map (gappedSubcomplex m C).ι)
        (completionRelativeSTranspose_inclusion r ι f hf m n)).trans
          ((completionRelativeSTransposeDiagram_inclusion r ι f hf m n).trans
            (Category.assoc _ _ _).symm))
  have hG : G ≫ a = b ≫ t :=
    (Category.assoc G (gappedSubcomplex m R).ι ((ihom (arNerve m)).map I)).symm.trans
      ((congrArg (fun h => h ≫ (ihom (arNerve m)).map I)
        (gappedFamilyLift_ι (completionRelativeSInverseDiagram r ι f hf m n)
          (completionRelativeSInverseDiagram_isGapped r ι f hf m n))).trans
            ((completionRelativeSInverseDiagram_inclusion r ι f hf m n).trans
              (Category.assoc _ _ _).symm))
  exact ⟨F, G,
    inverse_comp_of_commuting_mono a b F G s t hF hG (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.internalHomSwap_twice _ _ _),
    inverse_comp_of_commuting_mono b a G F t s hG hF (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.internalHomSwap_twice _ _ _)⟩

end SerrePositivity.KST.SConstruction.Cofinality
