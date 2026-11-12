module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeSInverseDiagram

/-!
概要：元の相対 S 旗の逆転置は前段の相対旗値で gapped となる。
方針：全部分旗の包含後に元の旗を回収し、点ごとの gapped 性を反映する。
規約：元の零図式と元の包含を保持する。
使われ方：相対旗の S 交換の逆射。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の逆転置の族は包含後に元の二重内部 Hom の射を回収する。
方針：全部分圏の内部 Hom の逆比較と持ち上げの包含公式を合成する。
規約：元の全高次単体の等号。
使われ方：逆転置の gapped 性の反映。 -/
lemma completionRelativeSInverseDiagram_inclusion (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory) :
    completionRelativeSInverseDiagram r ι f hf m n ≫
      (ihom (arNerve m)).map (completionRelativeFlagAmbientMap r ι f hf n).val =
        completionRelativeSRawInverse r ι f hf m n := by
  let P := multiRelativeFlagPredicate r ι Y
    (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex (stdSimplex.obj n)
  let C := (ihom (stdSimplex.obj n)).obj (((multiSEndofunctor r).obj ι).obj Y).carrier
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (completionRelativeSRawInverse r ι f hf m n)
    (completionRelativeSRawInverse_relative r ι f hf m n)
  let B := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomBackward (arNerve m) C P
  have he : B ≫ (ihom (arNerve m)).map
      (completionRelativeFlagAmbientMap r ι f hf n).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies (arNerve m) C P)).ι :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomBackward_ι (arNerve m) C P
  exact (Category.assoc L B ((ihom (arNerve m)).map
    (completionRelativeFlagAmbientMap r ι f hf n).val)).trans
      ((congrArg (fun h => L ≫ h) he).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _))

/-- 概要：逆転置の元の Ar 図式は包含後に元の旗の転置を回収する。
方針：族の包含公式を元の関手頂点の表示へ移す。
規約：元の旗の代表を変更しない。
使われ方：点ごとの gapped 条件の照合。 -/
lemma completionRelativeSInverseDiagram_vertex_inclusion (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory)
    (v : (completionRelativeFlagStableModel (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι)
      f hf n).carrier _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m) (completionRelativeFlagStableModel r ι f hf n).carrier).symm
        ((completionRelativeSInverseDiagram r ι f hf m n).app (Opposite.op ⦋0⦌) v) ≫
      (completionRelativeFlagAmbientMap r ι f hf n).val =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (stdSimplex.obj n) (arNerve m)
          (((multiSEndofunctor r).obj ι).obj Y).carrier
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n)
            (sStableModel m (((multiSEndofunctor r).obj ι).obj Y)).carrier).symm v.val ≫
              (gappedSubcomplex m (((multiSEndofunctor r).obj ι).obj Y).carrier).ι) := by
  have h := congrArg (fun h => h.app (Opposite.op ⦋0⦌) v)
    (completionRelativeSInverseDiagram_inclusion r ι f hf m n)
  exact (diagramVertex_postcomp (completionRelativeFlagAmbientMap r ι f hf n).val
    ((completionRelativeSInverseDiagram r ι f hf m n).app (Opposite.op ⦋0⦌) v)).symm.trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m)
        ((ihom (stdSimplex.obj n)).obj (((multiSEndofunctor r).obj ι).obj Y).carrier)).symm h).trans
          ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m)
            ((ihom (stdSimplex.obj n)).obj (((multiSEndofunctor r).obj ι).obj Y).carrier)).symm
              (completionRelativeSRawInverse_vertex r ι f hf m n v)).trans
                ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _)))

/-- 概要：逆転置した元の相対旗値の Ar 図式は gapped。
方針：元の全部分旗包含で反映し、各旗頂点で元の S 図式を回収する。
規約：元の零角と押し出し条件を保持する。
使われ方：元の S 構成への逆射の持ち上げ。 -/
lemma completionRelativeSInverseDiagram_isGapped (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory)
    (v : (completionRelativeFlagStableModel (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι)
      f hf n).carrier _⦋0⦌) :
    IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m)
      (completionRelativeFlagStableModel r ι f hf n).carrier).symm
        ((completionRelativeSInverseDiagram r ι f hf m n).app (Opposite.op ⦋0⦌) v)) := by
  apply IsGapped.of_fullSubcomplex (multiRelativeFlagPredicate r ι Y
    (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex (stdSimplex.obj n))
  apply (congrArg IsGapped
    (completionRelativeSInverseDiagram_vertex_inclusion r ι f hf m n v)).mpr
  apply (isGapped_functor_iff_pointwise _).mpr
  intro b
  rw [flipFamily_evaluate]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n)
      (sStableModel m (((multiSEndofunctor r).obj ι).obj Y)).carrier).symm v.val).app
        (Opposite.op ⦋0⦌) b)

/-- 概要：次段の元の相対旗から前段の元の相対旗の S 構成への逆射。
方針：同じ逆転置の全頂点の gapped 性で族全体を持ち上げる。
規約：元の全単体と元の包含を保持する。
使われ方：相対旗の S 交換同型の逆向き。 -/
def completionRelativeSInverse (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory) :
    (completionRelativeFlagStableModel (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι)
      f hf n).carrier ⟶
        (sStableModel m (completionRelativeFlagStableModel r ι f hf n)).carrier :=
  gappedFamilyLift (completionRelativeSInverseDiagram r ι f hf m n)
    (completionRelativeSInverseDiagram_isGapped r ι f hf m n)

end SerrePositivity.KST.SConstruction.Cofinality
