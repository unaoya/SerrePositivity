module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagInclusionExact
public import SerrePositivity.KST.SConstruction.SInterchangeTranspose

/-!
概要：元の相対旗の S 構成を、同じ S 模型値の標準単体上の旗へ転置する。
方針：元の全旗包含と内部 Hom の交換を使い、点ごとの gapped 条件を完全評価で示す。
規約：ここでは標的旗の分母条件をまだ結論しない。
使われ方：元の相対旗と S 構成との交換比較の順方向。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の相対 S 旗の二重関手圏への転置。
方針：元の全旗包含後に内部 Hom の二方向を交換する。
規約：元の反復 S 標的と旗の全高次単体を保持する。
使われ方：点ごとの gapped 性を検査する生の比較射。 -/
def completionRelativeSRawTranspose (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory) :
    (sStableModel m (completionRelativeFlagStableModel r ι f hf n)).carrier ⟶
      (ihom (stdSimplex.obj n)).obj ((ihom (arNerve m)).obj
        (((multiSEndofunctor r).obj ι).obj Y).carrier) :=
  (gappedSubcomplex m (completionRelativeFlagStableModel r ι f hf n).carrier).ι ≫
    (ihom (arNerve m)).map (completionRelativeFlagAmbientMap r ι f hf n).val ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve m) (stdSimplex.obj n)
        (((multiSEndofunctor r).obj ι).obj Y).carrier).hom

/-- 概要：生の転置の各頂点は元の gapped 族を転置した関手。
方針：元の関手頂点表示と内部 Hom の交換の公式を使う。
規約：元の全旗包含を保持する。
使われ方：転置の各成分の gapped 性。 -/
lemma completionRelativeSRawTranspose_vertex (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory)
    (v : (sStableModel m (completionRelativeFlagStableModel r ι f hf n)).carrier _⦋0⦌) :
    (completionRelativeSRawTranspose r ι f hf m n).app (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve m) (stdSimplex.obj n)
        (((multiSEndofunctor r).obj ι).obj Y).carrier
        (gappedDiagram v ≫ (completionRelativeFlagAmbientMap r ι f hf n).val)) := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m)
      (completionRelativeFlagStableModel r ι f hf n).carrier).apply_symm_apply v.val
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve m) (stdSimplex.obj n)
    (((multiSEndofunctor r).obj ι).obj Y).carrier).hom.app (Opposite.op ⦋0⦌)
      (((ihom (arNerve m)).map (completionRelativeFlagAmbientMap r ι f hf n).val).app
        (Opposite.op ⦋0⦌) v.val) = _
  rw [← hv]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_functorVertex (arNerve m) (stdSimplex.obj n)
    (((multiSEndofunctor r).obj ι).obj Y).carrier
    (gappedDiagram v ≫ (completionRelativeFlagAmbientMap r ι f hf n).val)

/-- 概要：元の転置の全旗頂点の Ar[m] 図式は gapped。
方針：元の相対旗包含と標準単体の頂点評価の完全性を合成する。
規約：頂点ごとに別の gapped 図式を選ばない。
使われ方：同じ反復 S 模型を値とする旗への持ち上げ。 -/
lemma completionRelativeSRawTranspose_gapped (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory)
    (s : (stdSimplex.obj n ⊗
      (sStableModel m (completionRelativeFlagStableModel r ι f hf n)).carrier) _⦋0⦌) :
    IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m)
      (((multiSEndofunctor r).obj ι).obj Y).carrier).symm
      ((uncurry (completionRelativeSRawTranspose r ι f hf m n)).app (Opposite.op ⦋0⦌) s)) := by
  rcases s with ⟨b, v⟩
  change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m)
    (((multiSEndofunctor r).obj ι).obj Y).carrier).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b).app (Opposite.op ⦋0⦌)
      ((completionRelativeSRawTranspose r ι f hf m n).app (Opposite.op ⦋0⦌) v)))
  rw [completionRelativeSRawTranspose_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, flipFamily_vertex]
  exact (gappedDiagram_isGapped v).postcomp _
    ((completionRelativeFlagAmbientMap r ι f hf n).property.toSConstructionData.comp
      (evaluateFunctorAt_preservesSConstructionData b))

/-- 概要：元の相対 S 旗を同じ S_m 標的上の全旗へ転置する。
方針：生の転置の全成分の gapped 性で族全体を持ち上げる。
規約：標的の分母旗条件は後続で検査する。
使われ方：相対旗の S 交換の具体的な順射。 -/
def completionRelativeSTransposeDiagram (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory) :
    (sStableModel m (completionRelativeFlagStableModel r ι f hf n)).carrier ⟶
      (ihom (stdSimplex.obj n)).obj
        (sStableModel m (((multiSEndofunctor r).obj ι).obj Y)).carrier :=
  curry (gappedFamilyLift (uncurry (completionRelativeSRawTranspose r ι f hf m n))
    (completionRelativeSRawTranspose_gapped r ι f hf m n))

end SerrePositivity.KST.SConstruction.Cofinality
