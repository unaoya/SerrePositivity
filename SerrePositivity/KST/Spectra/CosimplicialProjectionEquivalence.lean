module

public import SerrePositivity.KST.Spectra.CosimplicialTwoProjections

/-!
概要：余単体の二射影分解の各段における全基点 π_* 同型。
方針：anodyne な比較と厳密な合成式から参照頂点付きの消去則を使う。
規約：中間の各値の Kan 性を明示する。
使われ方：Goerss–Jardine VII §4、VIII §1。Tot の一般の係数比較の入力。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.CosimplicialTwoProjections

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : CosimplicialObject SSet.{u}} (f : X ⟶ Y)

/-- 概要：二射影分解の比較は各段の全基点 π_* 同型。
方針：各段が anodyne な Kan 複体間の射であることを使う。
規約：始域と中間の各値の Kan 性を仮定する。
使われ方：Goerss–Jardine VII §4。二射影の同型性の消去。 -/
lemma inclusion_levelwise [∀ j, KanComplex (X.obj j)] [∀ j, KanComplex ((obj f).obj j)]
    (j : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := X.obj j) (Y := (obj f).obj j) ((inclusion f).app j) :=
  kanPiIsomorphism_of_anodyne _ (inclusion_anodyne f j)

/-- 概要：元の始域への射影は各段の全基点 π_* 同型。
方針：anodyne な比較との合成が恒等射であることから消去する。
規約：元の各段の頂点を明示する。
使われ方：Goerss–Jardine VIII §1。Tot の比較の切断。 -/
lemma sourceProjection_levelwise
    [∀ j, KanComplex (X.obj j)] [∀ j, KanComplex ((obj f).obj j)]
    (e₀ : ∀ j, X.obj j _⦋0⦌) (j : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := (obj f).obj j) (Y := X.obj j) ((sourceProjection f).app j) := by
  have he := congr_app (inclusion_sourceProjection f) j
  change (inclusion f).app j ≫ (sourceProjection f).app j = 𝟙 (X.obj j) at he
  have h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((inclusion f).app j ≫ (sourceProjection f).app j) := by
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _
  exact (_root_.SerrePositivity.KST.Spectra.KanPiIsomorphism.cancel_left_atVertex (inclusion_levelwise f j)) h (e₀ j)

/-- 概要：元の射が各段の π_* 同型なら終域への射影も各段の π_* 同型。
方針：anodyne な比較との合成が元の射であることから消去する。
規約：全ての基点と零次数を含む。
使われ方：Goerss–Jardine VIII §1。Tot の比較の第二射影。 -/
lemma targetProjection_levelwise
    [∀ j, KanComplex (X.obj j)] [∀ j, KanComplex (Y.obj j)]
    [∀ j, KanComplex ((obj f).obj j)]
    (hf : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app j))
    (e₀ : ∀ j, X.obj j _⦋0⦌) (j : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := (obj f).obj j) (Y := Y.obj j) ((targetProjection f).app j) := by
  have he := congr_app (inclusion_targetProjection f) j
  change (inclusion f).app j ≫ (targetProjection f).app j = f.app j at he
  have h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((inclusion f).app j ≫ (targetProjection f).app j) := by
    rw [he]
    exact hf j
  exact (_root_.SerrePositivity.KST.Spectra.KanPiIsomorphism.cancel_left_atVertex (inclusion_levelwise f j)) h (e₀ j)

end

end SerrePositivity.KST.Spectra.CosimplicialTwoProjections
