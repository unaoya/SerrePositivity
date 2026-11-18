module
public import SerrePositivity.KST.SConstruction.Cofinality.CanonicalComponentProjection
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicialWeak

/-!
概要：元の全 S 多次数の wide 図式の先頭実現を成分障害へ離散化する。
方針：自然な成分射影の各段の弱同値を元の対角へ移す。
規約：射影に自然性を要求し、非自然な切断は各段の弱同値の証明だけに使う。
使われ方：元の wide 実現の障害を群 nerve へ接続する。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicial

/-- 概要：元の全多次数 wide 図式から元の成分の定値図式への自然変換。
方針：構成済みの元の成分射影と全多次数自然性を束ねる。
規約：選択した切断を自然変換に使わない。
使われ方：元の対角の離散化射。 -/
def completionCanonicalComponentProjectionNat (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionCanonicalWideDiagram r f hf ⟶
      completionWideComponentDiagram r f hf ⋙ Functor.const SimplexCategoryᵒᵖ where
  app ι := completionCanonicalComponentProjection r ι f
  naturality {_ _} α := completionCanonicalComponentProjection_naturality r α f hf

/-- 概要：元の全辺 wide 図式の先頭方向と内部単体方向の対角。
方針：残りの全多次数を固定して元の対角関手を適用する。
規約：各段の Kan 性を対角の Kan 性へ読み替えない。
使われ方：相対旗の評価が比較する元の wide 実現。 -/
def completionWideHeadRealization (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj
    (completionCokernelHeadIndex r ι ⋙ completionCanonicalWideDiagram (r + 1) f hf)

/-- 概要：元の wide の先頭対角実現から元の成分障害図式への射。
方針：自然な成分射影を対角へ移し、内側定値の対角同型を合成する。
規約：同じ未置換の成分射影を使う。
使われ方：元の wide 実現の障害の高次消滅。 -/
def completionWideHeadDiscretization (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionWideHeadRealization r ι f hf ⟶
      (completionCokernelHeadIndex r ι ⋙ completionWideComponentDiagram (r + 1) f hf) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (Functor.whiskerLeft (completionCokernelHeadIndex r ι)
    (completionCanonicalComponentProjectionNat (r + 1) f hf)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso (completionCokernelHeadIndex r ι ⋙
        completionWideComponentDiagram (r + 1) f hf)).hom

/-- 概要：元の wide の先頭対角実現の離散化は弱ホモトピー同値。
方針：全行の元の成分射影の弱同値をモデル不要の対角定理へ渡す。
規約：元の射そのものの弱同値性を結論する。
使われ方：bar 障害から元の wide 実現への移送。 -/
lemma completionWideHeadDiscretization_isWeak (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (completionWideHeadDiscretization r ι f hf) := by
  let τ := Functor.whiskerLeft (completionCokernelHeadIndex r ι)
    (completionCanonicalComponentProjectionNat (r + 1) f hf)
  have hτ (n : SimplexCategoryᵒᵖ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (τ.app n) :=
    completionCanonicalComponentProjection_isWeak (r + 1)
      ((completionCokernelHeadIndex r ι).obj n) f hf
  have hd := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicial.diagonalFunctor_map_weak τ hτ
  exact hd.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso
    (completionCokernelHeadIndex r ι ⋙
      completionWideComponentDiagram (r + 1) f hf))).isWeakHomotopyEquivalence

end SerrePositivity.KST.SConstruction.Cofinality
