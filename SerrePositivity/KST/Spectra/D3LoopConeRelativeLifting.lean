module

public import SerrePositivity.KST.Spectra.D3LoopSourceCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.F1BFibrationsRightAnodyneTensor

/-!
概要：実 loop cospan 上の錐比較と apex の比較を同時に保持する相対充填。
方針：右 fibration の相対内部 Hom を取り、右一次ホーンとの pushout-product で全単射 RLP を証明する。
規約：元の cospan を固定した全パラメータ。始点を動かす豊穣 Hom の合成はまだ主張しない。
使われ方：d3b② の図式比較を、頂点だけでなく既存の部分パラメータ上も固定して延長する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet MorphismProperty
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance loopConeRelativeSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance loopConeRelativeHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 元の cospan 上の終端錐と、全 apex 比較を同時に指定する相対内部 Hom。 -/
def loopConeLiftCornerSquare (X : OmegaSpectrum.{u}) :
    internalHom.PullbackObjObj (horn 1 1 : (Δ[1] : SSet.{u + 1}).Subcomplex).ι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (BasedLoop.diagram (tail X))) :=
  Functor.PullbackObjObj.ofHasPullback internalHom (horn 1 1).ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (BasedLoop.diagram (tail X)))

/-- 終端錐・apex 比較を同時に記憶する指定境界空間。 -/
abbrev loopConeLiftBoundary (X : OmegaSpectrum.{u}) : SSet.{u + 1} :=
  (loopConeLiftCornerSquare X).pt

/-- 全錐比較を、その指定終端と全 apex 比較へ写す元の射。 -/
def loopConeLiftCorner (X : OmegaSpectrum.{u}) :
    (ihom (Δ[1] : SSet.{u + 1})).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (BasedLoop.diagram (tail X))) ⟶
      loopConeLiftBoundary X :=
  (loopConeLiftCornerSquare X).π

/-- 終端錐と apex 比較を同時に固定しても、全単射の相対充填がある。 -/
instance loopConeLiftCorner_trivialKanFibration (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (loopConeLiftCorner X) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalTrivialKanFibration_relativeHom_of_rightAnodyne (horn 1 1).ι _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (BasedLoop.diagram (tail X))) (loopConeLiftCornerSquare X)
  intro E B p hp
  exact hp _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro (1 : Fin 2) (by decide))

/-- 部分パラメータに既存の実錐比較を固定し、同じ指定二境界上で延長する。 -/
lemma exists_relative_loopConeLift (X : OmegaSpectrum.{u}) {V U : SSet.{u + 1}}
    (j : V ⟶ U) [Mono j]
    (a : V ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (BasedLoop.diagram (tail X))))
    (b : U ⟶ loopConeLiftBoundary X) (h : a ≫ loopConeLiftCorner X = j ≫ b) :
    ∃ d : U ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (BasedLoop.diagram (tail X))),
      j ≫ d = a ∧
      d ≫ (pre (horn 1 1).ι).app _ = b ≫ (loopConeLiftCornerSquare X).fst ∧
      d ≫ (ihom (Δ[1] : SSet.{u + 1})).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (BasedLoop.diagram (tail X))) =
          b ≫ (loopConeLiftCornerSquare X).snd := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := loopConeLiftCorner X) j inferInstance
  let sq : CommSq a j (loopConeLiftCorner X) b := ⟨h⟩
  refine ⟨sq.lift, sq.fac_left, ?_, ?_⟩
  · have hf := congrArg (· ≫ (loopConeLiftCornerSquare X).fst) sq.fac_right
    simp only [Category.assoc, loopConeLiftCorner, Functor.PullbackObjObj.π_fst] at hf
    exact hf
  · have hf := congrArg (· ≫ (loopConeLiftCornerSquare X).snd) sq.fac_right
    simp only [Category.assoc, loopConeLiftCorner, Functor.PullbackObjObj.π_snd] at hf
    exact hf

/-- 同じ終端錐と全 apex 比較を固定した、実錐比較の選択空間は可縮。 -/
lemma loopConeLiftFiber_isContractibleKan (X : OmegaSpectrum.{u})
    (b : (loopConeLiftBoundary X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (loopConeLiftCorner X) b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan (loopConeLiftCorner X) b

/-- 構成済みの同じ実錐比較が指定する二境界。 -/
def loopSourceConeBoundary (X : OmegaSpectrum.{u}) : (loopConeLiftBoundary X) _⦋0⦌ :=
  (loopConeLiftCorner X).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (loopSourceConeLift X))

/-- この二境界の第一射影は、構成済み錐比較の同じ終端制限。 -/
lemma loopSourceConeBoundary_fst (X : OmegaSpectrum.{u}) :
    (loopConeLiftCornerSquare X).fst.app _ (loopSourceConeBoundary X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((horn 1 1).ι ≫ loopSourceConeLift X) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (loopConeLiftCornerSquare X).π_fst _) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (loopSourceConeLift X))
  exact h

/-- 第二射影は、元の BF 右脚の同じ一次単体全体。 -/
lemma loopSourceConeBoundary_snd (X : OmegaSpectrum.{u}) :
    (loopConeLiftCornerSquare X).snd.app _ (loopSourceConeBoundary X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (loopSourceToBasedLoop X)).edge) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (loopConeLiftCornerSquare X).π_snd _) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (loopSourceConeLift X))
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
    (loopSourceConeLift X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (BasedLoop.diagram (tail X))) at h
  rw [loopSourceConeLift_projection] at h
  exact h

/-- 元の実錐比較を含み、同じ全 apex 辺と終端を固定する選択空間。 -/
def loopSourceConeChoiceSpace (X : OmegaSpectrum.{u}) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (loopConeLiftCorner X) (loopSourceConeBoundary X)

/-- 同じ元の比較は、選び直さずその選択空間の指定点となる。 -/
def loopSourceConeChosenPoint (X : OmegaSpectrum.{u}) : (loopSourceConeChoiceSpace X) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (loopSourceConeLift X), by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]; rfl⟩

/-- 指定 BF 辺と終端錐を保つ全比較の可縮性。 -/
lemma loopSourceConeChoiceSpace_isContractibleKan (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (loopSourceConeChoiceSpace X) :=
  loopConeLiftFiber_isContractibleKan X (loopSourceConeBoundary X)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
