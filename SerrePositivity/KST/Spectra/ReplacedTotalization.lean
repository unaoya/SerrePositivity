module

public import SerrePositivity.KST.Spectra.TotalizationHomotopyInvariance
public import SerrePositivity.KST.Spectra.CosimplicialKanMapEquivalence

/-!
概要：Reedy 置換後の通常の Tot の関手性・単位と任意の Kan 係数のホモトピー不変性。
方針：関手的 Reedy 置換と通常の Tot を合成し、両段階の π_* 同型保存を使う。
規約：通常の Tot と Bousfield–Kan end の比較はこのモジュールの主張に含めない。
使われ方：Goerss–Jardine VII §4、VIII §1。L9e の Tot の Kan 模型の係数比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CosimplicialTotalization

instance replacement_kanComplex (X : CosimplicialObject SSet.{u}) :
    KanComplex (obj (CosimplicialKanReplacement.functor.obj X)) :=
  kanComplex_replacement X

/-- 概要：Reedy 置換した通常の Tot の間の実際の射。
方針：係数の射を Reedy 置換し、Tot の関手へ渡す。
規約：係数の各値の Kan 性は射の定義には不要。
使われ方：Goerss–Jardine VIII §1。置換した Tot の自然な比較。 -/
def replacementMap {X Y : CosimplicialObject SSet.{u}} (f : X ⟶ Y) :
    obj (CosimplicialKanReplacement.functor.obj X) ⟶
      obj (CosimplicialKanReplacement.functor.obj Y) :=
  map (CosimplicialKanReplacement.functor.map f)

/-- 概要：任意の Kan 係数の各段の π_* 同型は Reedy 置換後の通常の Tot でも同型。
方針：Reedy 置換の各段の同型保存と Reedy Kan 図式の Tot の不変性を合成する。
規約：元の図式に Reedy 条件は不要。各段の始域の頂点を指定する。
使われ方：Goerss–Jardine VII §4、VIII §1。Tot の Kan 模型のホモトピー不変性。 -/
lemma replacementMap_piIsomorphism {X Y : CosimplicialObject SSet.{u}}
    [∀ j, KanComplex (X.obj j)] [∀ j, KanComplex (Y.obj j)]
    (f : X ⟶ Y) (hf : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app j)) (e₀ : ∀ j, X.obj j _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (replacementMap f) := by
  let : ∀ j, KanComplex ((CosimplicialKanReplacement.functor.obj X).obj j) :=
    fun j ↦ CosimplicialKanReplacement.kanComplex X j
  let : ∀ j, KanComplex ((CosimplicialKanReplacement.functor.obj Y).obj j) :=
    fun j ↦ CosimplicialKanReplacement.kanComplex Y j
  exact map_piIsomorphism (CosimplicialKanReplacement.functor.map f)
    (CosimplicialKanReplacement.terminal_rlp X) (CosimplicialKanReplacement.terminal_rlp Y)
    (CosimplicialKanReplacement.map_piIsomorphism f hf e₀)
    (fun j ↦ (CosimplicialKanReplacement.unit.app X).app j |>.app _ (e₀ j))

end CosimplicialTotalization

namespace PointedTotalization

/-- 概要：Reedy 置換後の通常の点つき Tot の実際の関手。
方針：二つの構成済みの関手を合成する。
規約：値は任意の入力で点つき Kan 複体。
使われ方：Goerss–Jardine VIII §1。L9e の置換した Tot。 -/
def replacementFunctor : CosimplicialObject PointedSimplicialSet.{u} ⥤
    PointedSimplicialSet.{u} :=
  PointedCosimplicialKanReplacement.functor ⋙ functor

/-- 概要：置換後の通常の点つき Tot の射への作用。
方針：合成関手の射を取り出す。
規約：始域・終域は既存の replacementObj。
使われ方：Goerss–Jardine VIII §1。Tot の Kan 模型の比較。 -/
def replacementMap {X Y : CosimplicialObject PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    replacementObj X ⟶ replacementObj Y := replacementFunctor.map f

/-- 概要：通常の点つき Tot から Reedy 置換後の Tot への自然な標準射。
方針：Reedy 置換の単位を Tot 関手で送る。
規約：元の Tot の Kan 性や比較射の同型性を定義には要求しない。
使われ方：Goerss–Jardine VIII §1。通常の Tot と置換した Tot の標準比較。 -/
def replacementUnit : functor ⟶ replacementFunctor :=
  Functor.whiskerRight PointedCosimplicialKanReplacement.unit functor

/-- 概要：点つき Kan 係数の各段の π_* 同型は置換後の通常の Tot でも同型。
方針：各基点を参照頂点として基礎図式の Tot の不変性を使う。
規約：元の係数の Reedy 条件は不要。
使われ方：Goerss–Jardine VII §4、VIII §1。点つき Tot の Kan 模型のホモトピー不変性。 -/
lemma replacementMap_piIsomorphism
    {X Y : CosimplicialObject PointedSimplicialSet.{u}}
    [∀ j, KanComplex (X.obj j).right] [∀ j, KanComplex (Y.obj j).right]
    (f : X ⟶ Y) (hf : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app j).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (replacementMap f).right := by
  let : ∀ j, KanComplex ((X ⋙ PointedSimplicialSet.forget).obj j) :=
    fun j ↦ inferInstanceAs (KanComplex (X.obj j).right)
  let : ∀ j, KanComplex ((Y ⋙ PointedSimplicialSet.forget).obj j) :=
    fun j ↦ inferInstanceAs (KanComplex (Y.obj j).right)
  exact CosimplicialTotalization.replacementMap_piIsomorphism
    (Functor.whiskerRight f PointedSimplicialSet.forget) hf
    (fun j ↦ PointedSimplicialSet.basepoint (X.obj j))

end PointedTotalization

end

end SerrePositivity.KST.Spectra
