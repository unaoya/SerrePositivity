module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：quasicategory 間の inner anodyne 射の同値性。
方針：逆射を延長し、制限の内部 Hom の可縮な fiber で可逆二胞体を作る。
規約：inner anodyne 性は生成ホーンの llp として用いる。
使われ方：Kerodon §4.5.3（Tag 032Y）–4.5.4（Tag 01E7）、Theorem 4.8.4.1（Tag 01JX）。

対応節は Kerodon 1.5（Tag 0055）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories

/-- 概要：inner anodyne 射に沿った関手の制限は trivial Kan fibration。
方針：境界との pushout-product の inner anodyne 性と内部 Hom の随伴を使う。
規約：標的は quasicategory、始域の quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y）–4.5.4（Tag 01E7） の相対的な関手のホモトピー。 -/
@[kerodon 00J9]
lemma trivialKanFibration_pre_of_innerAnodyne {A B : SSet.{u}} (i : A ⟶ B)
    (hi : innerAnodyneExtensions i) (Y : SSet.{u}) [Quasicategory Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre i).app Y) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i (boundary n).ι
  let sq' := Functor.PullbackObjObj.ofIsTerminal internalHom i (terminal.from Y) terminalIsTerminal
  change HasLiftingProperty (boundary n).ι sq'.π
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  exact (innerAnodyneExtensions_pushoutObjObjι' sq hi) _ (InnerFibration.mem (q := terminal.from Y))

/-- 概要：quasicategory を始域とする inner anodyne 射には厳密な引き戻しが存在する。
方針：始域の終対象への inner fibration に対して恒等射を延長する。
規約：i の後で r を適用すると始域の恒等射。
使われ方：Kerodon §4.5.3（Tag 032Y） の同値の逆射。 -/
lemma innerAnodyne_exists_retraction {A B : SSet.{u}} [Quasicategory A]
    (i : A ⟶ B) (hi : innerAnodyneExtensions i) : ∃ r : B ⟶ A, i ≫ r = 𝟙 A := by
  have := hi (terminal.from A) (InnerFibration.mem (q := terminal.from A))
  have sq : CommSq (𝟙 A) i (terminal.from A) (terminal.from B) := ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：quasicategory 間の inner anodyne 射から A3a の明示的な同値を得る。
方針：厳密な引き戻しを逆射とし、関手の制限の可縮 fiber で余単位を作る。
規約：順方向の射は i そのもの。
使われ方：Kerodon §4.5.3（Tag 032Y）–4.5.4（Tag 01E7）、Theorem 4.8.4.1（Tag 01JX）。 -/
noncomputable def qCatEquivalenceOfInnerAnodyne {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (i : A ⟶ B) (hi : innerAnodyneExtensions i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A B := by
  let r := Classical.choose (innerAnodyne_exists_retraction i hi)
  have hr : i ≫ r = 𝟙 A := Classical.choose_spec (innerAnodyne_exists_retraction i hi)
  let q := (pre i).app B
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q := trivialKanFibration_pre_of_innerAnodyne i hi B
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex i
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan q b
  have := hc.kanComplex
  let v₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (r ≫ i), by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ (r ≫ i)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex i
    rw [← Category.assoc, hr, Category.id_comp]⟩
  let v₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 B), by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ (𝟙 B)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex i
    rw [Category.comp_id]⟩
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex v₀) (hc.isTerminalVertex v₁)
  refine { hom := i
           inv := r
           homInvIso := ?_
           invHomIso := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map h (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b) }
  exact eqToIso (congrArg (fun f : A ⟶ A ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) hr)

/-- 概要：quasicategory 間の inner anodyne 射は同値という性質を持つ。
方針：明示的な逆データの存在を使う。
規約：追加のモデル構造の同値性は用いない。
使われ方：Kerodon Theorem 4.8.4.1（Tag 01JX） のファイブレーションへの還元。 -/
lemma isQCatEquivalence_of_innerAnodyne {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (i : A ⟶ B) (hi : innerAnodyneExtensions i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence i := (qCatEquivalenceOfInnerAnodyne i hi).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories
