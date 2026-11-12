module
public import SerrePositivity.KST.SConstruction.FrameFirstRow

/-! # gapped 図式から零対角の枠への制限
概要：第一行制限を零対角の補完段階を通じて因子分解する。
方針：Ar[n] の枠への前合成が零対角条件を保つことを使う。
規約：cofiber 補完の同値性は別に証明する。使われ方：BGT Lemma 7.3。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：枠の nerve を Ar[n] に含める。
方針：順序包含の nerve。
規約：全ての鎖を保持する。使われ方：gapped 図式の零対角枠への制限。 -/
def frameInclusion (n : ℕ) : frameNerve.{u} n ⟶ arNerve n :=
  nerveMap (frameForgetOrder n).toFunctor

/-- 概要：枠の第一行を Ar[n] へ送ると元の第一行包含となる。
方針：順序包含の合成を計算する。
規約：厳密等号。使われ方：第一行制限の因子分解。 -/
lemma firstRowFrameMap_inclusion (n : ℕ) :
    firstRowFrameMap n ≫ (framePositiveRow n).ι ≫ frameInclusion.{u} n = firstRowInclusion n := rfl

/-- 概要：gapped 図式は枠上の対角で零対象となる。
方針：対角区間を (i,i) と書き直し、gapped の零対角条件を使う。
規約：quasicategory 性は不要。使われ方：枠への制限の頂点条件。 -/
lemma IsGapped.zeroFrameVertex {n : ℕ} {C : SSet.{u}} {F : arNerve n ⟶ C}
    (hF : IsGapped F) : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (frameInclusion n ≫ F)) := by
  intro x hd
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  let a := (nerveEquiv x).val
  have hx : x = ComposableArrows.mk₀ (nerveEquiv x) := (nerveEquiv.symm_apply_apply x).symm
  rw [hx]
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a))
  have ha : a = arObj a.down.val.1 a.down.val.1 le_rfl := by
    apply ULift.ext
    apply Subtype.ext
    exact Prod.ext rfl hd.symm
  rw [ha]
  exact hF.1 _

/-- 概要：gapped 図式を零対角の枠へ制限する。
方針：内部 Hom の前合成を、零対角の頂点条件による全部分複体に持ち上げる。
規約：全ての選択を保持する。使われ方：cofiber 補完の忘却射。 -/
def gappedFrameRestriction (n : ℕ) (C : SSet.{u}) :
    sConstruction n C ⟶ zeroFrameDiagrams n C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ ((gappedSubcomplex n C).ι ≫ (pre (frameInclusion n)).app C) (by
    intro v
    have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v) = v.val :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).apply_symm_apply v.val
    change IsZeroFrameVertex (((pre (frameInclusion n)).app C).app (Opposite.op ⦋0⦌) v.val)
    rw [← hv]
    exact (gappedDiagram_isGapped v).zeroFrameVertex)

/-- 概要：零対角の枠から元の添字の第一行への制限。
方針：枠内の第一行と Fin n の nerve の同型で前合成する。
規約：値域は firstRowRestriction と同じ。使われ方：第一行制限の因子分解。 -/
def frameRowRestriction (n : ℕ) (C : SSet.{u}) :
    zeroFrameDiagrams n C ⟶ (ihom (firstRowNerve n)).obj C :=
  zeroFrameProjection n C ≫ (pre (frameFirstRowIso n).hom).app C

/-- 概要：第一行制限は零対角の枠を通じて厳密に因子分解する。
方針：全部分複体の包含後で前合成の合成則を使う。
規約：元の S_n の定義を変更しない。使われ方：残る cofiber 補完段階の切り出し。 -/
lemma firstRowRestriction_factor (n : ℕ) (C : SSet.{u}) :
    gappedFrameRestriction n C ≫ frameRowRestriction n C = firstRowRestriction n C := by
  dsimp only [frameRowRestriction, zeroFrameProjection]
  rw [← Category.assoc, ← Category.assoc]
  change (((gappedSubcomplex n C).ι ≫ (pre (frameInclusion n)).app C) ≫
    (pre (framePositiveRow n).ι).app C) ≫ (pre (frameFirstRowIso n).hom).app C = _
  rw [Category.assoc, Category.assoc, ← NatTrans.comp_app, ← pre_map,
    ← NatTrans.comp_app, ← pre_map]
  have hi : ((frameFirstRowIso n).hom ≫ (framePositiveRow n).ι) ≫ frameInclusion n =
      firstRowInclusion n := by
    rw [Category.assoc]
    exact firstRowFrameMap_inclusion n
  rw [hi]
  rfl

/-- 概要：第一行の二つの添字表示による内部 Hom は同型。
方針：前合成の反変性から同型を作る。
規約：値域 C は任意。使われ方：枠の射影の trivial Kan fibration の移送。 -/
def frameRowDiagramIso (n : ℕ) (C : SSet.{u}) :
    (ihom (framePositiveRow n : SSet.{u})).obj C ≅ (ihom (firstRowNerve n)).obj C where
  hom := (pre (frameFirstRowIso n).hom).app C
  inv := (pre (frameFirstRowIso n).inv).app C
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id]
    rfl
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id, pre_id]
    rfl

/-- 概要：零対角の枠から元の第一行への制限は trivial Kan fibration。
方針：枠内の第一行への射影に添字の同型を合成する。
規約：零対象の存在だけで成立する。使われ方：第一行の cofiber 補完との分離。 -/
instance frameRowRestriction_trivialKanFibration (n : ℕ) (C : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (frameRowRestriction n C) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (zeroFrameProjection n C ≫ (frameRowDiagramIso n C).hom)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

end SerrePositivity.KST.SConstruction
