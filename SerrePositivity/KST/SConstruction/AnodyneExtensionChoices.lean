module
public import SerrePositivity.KST.SConstruction.GappedPointwiseColimit
public import SerrePositivity.KST.Spectra.AnodyneMappingLifts
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan

/-! # 基点を持たない anodyne 延長の選択空間
概要：Kan 標的への射の anodyne 延長を全パラメーターで制御する。
方針：内部 Hom の制限の厳密な fiber を取る。
規約：パラメーター空間に不要な基点条件を課さない。
使われ方：自然性の二重円筒の Kan 置換への延長の高次選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalClosed SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の射を厳密に制限として持つ延長の選択空間。 -/
def anodyneExtensionChoices {A B Z : SSet.{u}} (i : A ⟶ B) (h : A ⟶ Z) : SSet.{u} :=
  pullback ((pre i).app Z) (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h))

/-- 延長の選択空間の一点への射影は trivial Kan fibration。 -/
lemma anodyneExtensionChoices_projection_trivialKanFibration {A B Z : SSet.{u}}
    [KanComplex Z] (i : A ⟶ B) (hi : anodyneExtensions i) (h : A ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.snd ((pre i).app Z) (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h))) := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre i).app Z) := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyne_pre_rlp_monomorphisms i hi Z⟩
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.pullback_snd _ _ hp.mem⟩

/-- anodyne 延長の全選択空間は可縮 Kan。 -/
lemma anodyneExtensionChoices_isContractibleKan {A B Z : SSet.{u}} [KanComplex Z]
    (i : A ⟶ B) (hi : anodyneExtensions i) (h : A ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (anodyneExtensionChoices i h) := by
  have hp := anodyneExtensionChoices_projection_trivialKanFibration i hi h
  intro n a
  have := hp.mem (boundary n).ι inferInstance
  let sq : CommSq a (boundary n).ι
      (pullback.snd ((pre i).app Z) (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h)))
      (stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u})) :=
    ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 延長の選択の任意のパラメーター族を既存部分を保って補完できる。 -/
lemma anodyneExtensionChoices_relative_lifting {A B Z : SSet.{u}} [KanComplex Z]
    (i : A ⟶ B) (hi : anodyneExtensions i) (h : A ⟶ Z)
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ anodyneExtensionChoices i h) :
    ∃ b : T ⟶ anodyneExtensionChoices i h, j ≫ b = a := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration _).mp
    (anodyneExtensionChoices_isContractibleKan i hi h)
  have := hc.mem j inferInstance
  let sq : CommSq a j (terminal.from (anodyneExtensionChoices i h)) (terminal.from T) :=
    ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 選択空間の頂点から実際の延長を取り出す。 -/
def anodyneExtensionAt {A B Z : SSet.{u}} (i : A ⟶ B) (h : A ⟶ Z)
    (v : (anodyneExtensionChoices i h) _⦋0⦌) : B ⟶ Z :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B Z).symm
    ((pullback.fst ((pre i).app Z) (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h))).app (Opposite.op ⦋0⦌) v)

/-- 取り出した延長は元の射を厳密に回収する。 -/
lemma anodyneExtensionAt_fac {A B Z : SSet.{u}} (i : A ⟶ B) (h : A ⟶ Z)
    (v : (anodyneExtensionChoices i h) _⦋0⦌) : i ≫ anodyneExtensionAt i h v = h := by
  have hc := ConcreteCategory.congr_hom (NatTrans.congr_app
    (pullback.condition (f := (pre i).app Z)
      (g := SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h))) (Opposite.op ⦋0⦌)) v
  have hv : (pullback.snd ((pre i).app Z) (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h))).app
      (Opposite.op ⦋0⦌) v = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.objEquiv.injective
    exact Subsingleton.elim _ _
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hc
  rw [hv, SSet.yonedaEquiv_symm_app_id] at hc
  have hh := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A Z).symm hc
  rw [functorVertexEquiv_symm_pre] at hh
  exact hh.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A Z).symm_apply_apply h)

end SerrePositivity.KST.SConstruction
