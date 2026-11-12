module
public import SerrePositivity.KST.SConstruction.KanAssemblyHomotopyMaps
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead
public import SerrePositivity.KST.Spectra.UnbasedHomotopyIsomorphism
public import SerrePositivity.KST.Spectra.CofibrantKanSequence

/-! # 反復 S の同一の Kan 列への接続
概要：一次方向の比較のホモトピー逆を使い、全零境界商の各 Kan 段を接続する。
方針：既証の π 同型に L9 の Whitehead を適用し、随伴射を前合成して uncurry する。
規約：第 r 段は r+1 重 S。Ω 条件は KanAssemblyEquivalence で証明する。
使われ方：BF 模型への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 概要：一次方向の Kan 比較の実際の点つきホモトピー逆。
方針：全基点 π 同型から L9 の Whitehead により逆射を選ぶ。
規約：厳密な逆ではない。使われ方：同一の反復列上の随伴射。 -/
def oneDirectionKanComparisonInverse (r : ℕ) (X : StableModel.{u}) :
    (boundaryKanRealizationFunctor r).obj X ⟶ (oneDirectionKanRealizationFunctor r).obj X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopyInverse ((oneDirectionKanComparisonNat r).app X)
    (oneDirectionReducedComparison_kan_piIsomorphism r X)).choose

/-- 概要：比較の後に逆射を合成すると源の恒等射と基点固定でホモトピック。
方針：Whitehead から選んだ逆射の第一の比較を取り出す。
規約：恒等射から合成への向き。使われ方：源模型の回収。 -/
lemma oneDirectionKanComparison_inverse_homotopy (r : ℕ) (X : StableModel.{u}) :
    ∃ H : SSet.Homotopy (𝟙 (((oneDirectionKanRealizationFunctor r).obj X).right))
      (((oneDirectionKanComparisonNat r).app X ≫ oneDirectionKanComparisonInverse r X).right),
      ((oneDirectionKanRealizationFunctor r).obj X).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          ((oneDirectionKanRealizationFunctor r).obj X).hom :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopyInverse ((oneDirectionKanComparisonNat r).app X)
    (oneDirectionReducedComparison_kan_piIsomorphism r X)).choose_spec.1

/-- 概要：逆射の後に比較を合成すると境界商の恒等射と基点固定でホモトピック。
方針：Whitehead から選んだ逆射の第二の比較を取り出す。
規約：恒等射から合成への向き。使われ方：同じ反復段の回収。 -/
lemma oneDirectionKanComparisonInverse_homotopy (r : ℕ) (X : StableModel.{u}) :
    ∃ H : SSet.Homotopy (𝟙 (((boundaryKanRealizationFunctor r).obj X).right))
      ((oneDirectionKanComparisonInverse r X ≫ (oneDirectionKanComparisonNat r).app X).right),
      ((boundaryKanRealizationFunctor r).obj X).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          ((boundaryKanRealizationFunctor r).obj X).hom :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopyInverse ((oneDirectionKanComparisonNat r).app X)
    (oneDirectionReducedComparison_kan_piIsomorphism r X)).choose_spec.2

/-- 概要：一次方向の比較の逆射も全基点 π 同型。
方針：合成と恒等射のホモトピー不変性から、比較の π 同型を打ち消す。
規約：零次数を含む。使われ方：段の接続の源の同値比較。 -/
lemma oneDirectionKanComparisonInverse_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (oneDirectionKanComparisonInverse r X).right := by
  obtain ⟨H, _⟩ := oneDirectionKanComparisonInverse_homotopy r X
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp
    ((Spectra.kanPiIsomorphism_iff_of_homotopy H).mp (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _))
    (oneDirectionReducedComparison_kan_piIsomorphism r X)

/-- 概要：元の境界商の Kan 段から次段の loop への随伴射。
方針：一次方向の比較の逆射と、構成済みの Kan 延長を合成する。
規約：追加の存在仮定なし。使われ方：同じ段の列の構造射。 -/
def boundaryKanAssemblyAdjoint (r : ℕ) (X : StableModel.{u}) :
    (boundaryKanRealizationFunctor r).obj X ⟶ (loopBoundaryKanFunctor (r + 1)).obj X :=
  oneDirectionKanComparisonInverse r X ≫ kanAssemblyAdjointAt r X
    (kanAssemblyAdjointChoices_isContractibleKan r X).nonempty.some

/-- 概要：同一の反復段の列を結ぶ suspension 構造射。
方針：構成した随伴射を L9 の smash と loop の随伴で戻す。
規約：第 r 段は r+1 重 S の全零境界商の Kan 置換。使われ方：Kan 列への束ね。 -/
def boundaryKanAssemblySigma (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((boundaryKanRealizationFunctor r).obj X) ⟶
      (boundaryKanRealizationFunctor (r + 1)).obj X :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _).symm (boundaryKanAssemblyAdjoint r X)

/-- 概要：suspension 構造射の随伴は構成した loop への射。
方針：随伴同値の逆方向の消去。
規約：厳密等号。使われ方：Ω 条件の検証対象の特定。 -/
lemma boundaryKanAssemblySigma_adjoint (r : ℕ) (X : StableModel.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _) (boundaryKanAssemblySigma r X) =
      boundaryKanAssemblyAdjoint r X := Equiv.apply_symm_apply _ _

/-- 概要：全零境界商の Kan 模型と実際の構造射を持つ反復 S の列。
方針：全ての段で同じ境界商の関手を使い、suspension 構造射で束ねる。
規約：Ω 条件は構造の入力にも結論にも含めない。使われ方：BF の単射置換の入力。 -/
def boundaryKanSequence (X : StableModel.{u}) : Spectra.KanSequence.{u} where
  level r := ⟨(boundaryKanRealizationFunctor r).obj X, inferInstance⟩
  sigma r := boundaryKanAssemblySigma r X

/-- 概要：反復 S の実際の Kan 列を単射構造射の列へ置換する。
方針：L9 の逐次的な点つき因子分解を適用する。
規約：全次数の構造射の源と標的はこの同一の列の段。使われ方：BF の単射条件。 -/
def monicBoundaryKanSequence (X : StableModel.{u}) : Spectra.KanSequence.{u} :=
  (boundaryKanSequence X).cofibrantReplacement

/-- 概要：置換した反復 S の列の全構造射は単射。
方針：L9 の列の単射置換の性質。
規約：底の単体集合の射について。使われ方：BF の構造射の単射条件。 -/
instance monicBoundaryKanSequence_sigma_mono (X : StableModel.{u}) (r : ℕ) :
    Mono ((monicBoundaryKanSequence X).sigma r).right :=
  Spectra.KanSequence.cofibrantReplacement_sigma_mono _ r

/-- 概要：単射構造射の列から元の境界商の列への厳密な比較射。
方針：逐次置換の射影を使う。
規約：全構造射と厳密可換。使われ方：元の反復 S の段との照合。 -/
def monicBoundaryKanSequenceProjection (X : StableModel.{u}) :
    Spectra.KanSequence.Hom (monicBoundaryKanSequence X) (boundaryKanSequence X) :=
  Spectra.KanSequence.replacementProjection _

/-- 概要：単射置換の比較は各段で全基点 π 同型。
方針：L9 の置換射影の定理を使う。
規約：零次数も含む。使われ方：単射な列と元の反復 S の比較。 -/
lemma monicBoundaryKanSequenceProjection_piIsomorphism (X : StableModel.{u}) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((monicBoundaryKanSequenceProjection X).app r).right :=
  Spectra.KanSequence.replacementProjection_piIsomorphism _ r

end SerrePositivity.KST.SConstruction
