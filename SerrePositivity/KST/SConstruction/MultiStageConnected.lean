module
public import SerrePositivity.KST.SConstruction.KStageHomotopyFunctor
public import SerrePositivity.KST.SConstruction.RealizationConnected
public import SerrePositivity.KST.SConstruction.ReducedMultiRealization

/-! # 反復 S の正の段の連結性
概要：正の回数の反復 S の実現・全零境界商・その Kan 模型は連結。
方針：同時零段の可縮性を対角へ移し、商の π₀ の全単射と anodyne 単位を使う。
規約：高い次数の消滅はまだ結論しない。使われ方：連結 K のスペクトルへの接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：正の回数の反復 core S の対角実現は連結。
方針：同時零段の可縮性から連結性を得て、零段から対角への全射で移す。
規約：対角の Kan 性は不要。使われ方：全零境界商の連結性。 -/
instance multiDiagonalCoreSConstruction_isConnected (r : ℕ) (X : StableModel.{u}) :
    SSet.IsConnected (multiDiagonalCoreSConstruction (r + 1) X) := by
  let M := (multiDiagonalDiagramFunctor (r + 1)).obj X
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (M.obj (Opposite.op ⦋0⦌)) :=
    multiDiagonalDiagram_zero_isContractibleKan r X
  let : SSet.IsPreconnected (M.obj (Opposite.op ⦋0⦌)) := hc.piZero_subsingleton
  let : SSet.IsConnected (M.obj (Opposite.op ⦋0⦌)) := ⟨hc.nonempty⟩
  exact diagonal_connected_of_zero M

/-- 概要：全零境界を潰す射影は連結成分で全単射。
方針：anodyne を反転する π₀ 関手へ、既証の商写像の可逆性を適用する。
規約：両端の Kan 性は不要。使われ方：境界商の連結性の移送。 -/
lemma boundaryReductionQuotient_piZero_bijective (r : ℕ) (X : StableModel.{u}) :
    Function.Bijective (SSet.mapπ₀ (boundaryReductionQuotient r X)) := by
  have hi := boundaryReductionQuotient_image_isIso SSet.π₀Functor
    PiZeroLocalization.inverts_anodyne r X
  exact (CategoryTheory.isIso_iff_bijective _).mp hi

/-- 概要：反復実現の全零境界商は連結。
方針：元の反復実現の連結成分を商の π₀ の全射で移す。
規約：r+1 重 S を使い、Kan 性は不要。使われ方：Kan 模型の連結性。 -/
instance boundaryReducedRealization_isConnected (r : ℕ) (X : StableModel.{u}) :
    SSet.IsConnected (boundaryReducedRealization r X).right := by
  have hs := (boundaryReductionQuotient_piZero_bijective r X).surjective
  let : SSet.IsPreconnected (boundaryReducedRealization r X).right := ⟨by
    intro a b
    obtain ⟨x, rfl⟩ := hs a
    obtain ⟨y, rfl⟩ := hs b
    exact congrArg (SSet.mapπ₀ (boundaryReductionQuotient r X)) (Subsingleton.elim x y)⟩
  exact ⟨⟨(boundaryReducedRealization r X).basepoint⟩⟩

/-- 概要：全零境界商の Kan 置換は連結。
方針：商の連結性を anodyne な点つき Kan 置換の単位で移す。
規約：全ての反復回数。使われ方：正のスペクトル候補段の連結性。 -/
instance boundaryKanRealization_isConnected (r : ℕ) (X : StableModel.{u}) :
    SSet.IsConnected (((boundaryKanRealizationFunctor r).obj X).right) :=
  isConnected_of_anodyne (A := (boundaryReducedRealization r X).right)
    (B := ((boundaryKanRealizationFunctor r).obj X).right)
    (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right
    (Spectra.PointedKanReplacement.unit_anodyne _)

/-- 概要：点つき Kan 複体の π 同型の標的が連結なら源も連結。
方針：零次数の実際の同値と π₀ への同値を使い、源の成分が高々一つであることを移す。
規約：非空性は源の基点から得る。使われ方：単射置換した段の連結性。 -/
lemma pointedIsConnected_of_piIsomorphism {A B : PointedSimplicialSet.{u}}
    [KanComplex A.right] [KanComplex B.right] [SSet.IsConnected B.right]
    (f : A ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right) : SSet.IsConnected A.right := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism 0 f.right hf
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f)
  let eA : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy A.right 0 A.basepoint ≃ SSet.π₀ A.right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
  let eB : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy B.right 0 B.basepoint ≃ SSet.π₀ B.right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
  let : SSet.IsPreconnected A.right := ⟨by
    intro a b
    apply eA.symm.injective
    apply e.injective
    apply eB.injective
    exact Subsingleton.elim _ _⟩
  exact ⟨⟨A.basepoint⟩⟩

/-- 概要：K の候補列の全ての正の段は連結。
方針：正の段は全零境界商の Kan 模型であることを使う。
規約：零段 K の連結性は主張しない。使われ方：連結スペクトルの検証。 -/
instance kKanSequence_positive_isConnected (X : StableModel.{u}) (r : ℕ) :
    SSet.IsConnected (((kKanSequence X).level (r + 1)).space).right :=
  boundaryKanRealization_isConnected r X

/-- 概要：単射構造射の K の候補列の全ての正の段は連結。
方針：置換射影の π 同型を使って元の正の段の連結性を移す。
規約：高次の連結性や Ω 条件を追加仮定しない。使われ方：BF の連結性への接続。 -/
instance monicKKanSequence_positive_isConnected (X : StableModel.{u}) (r : ℕ) :
    SSet.IsConnected (((monicKKanSequence X).level (r + 1)).space).right :=
  pointedIsConnected_of_piIsomorphism ((monicKKanSequenceProjection X).app (r + 1))
    (monicKKanSequenceProjection_piIsomorphism X (r + 1))

end SerrePositivity.KST.SConstruction
