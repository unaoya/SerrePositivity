module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.WeakHomotopyExtensionSpace

/-! # 実屋根の二段降下の可縮な空間

概要：屋根の評価と商への降下を、比較を含む一つの可縮な空間へ束ねる。
方針：評価の延長空間上で、商比較による前合成の path 置換を引き戻す。
規約：中間の屋根は Kan でなくてよい。使われ方：全高次パラメータにわたる降下の選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalClosed SSet

/-- 評価の戻し方と、屋根の商比較に沿う降下の全高次族。 -/
def weakRoofDescentSpace {R Q E Z : SSet.{u}} (w : R ⟶ Q) (i : Z ⟶ E) (t : R ⟶ E) :
    SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap ((pre w).app Z))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakHomotopyExtensionEvaluation i (𝟙 Z) ≫ (pre t).app Z)

/-- 二段降下の空間から、最初の評価の延長空間への射影。 -/
def weakRoofDescentProjection {R Q E Z : SSet.{u}} (w : R ⟶ Q) (i : Z ⟶ E) (t : R ⟶ E) :
    weakRoofDescentSpace w i t ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakHomotopyExtensionSpace i (𝟙 Z) :=
  pullback.snd _ _

/-- 商の屋根比較が弱同値なら、二段降下の射影は trivial Kan fibration。 -/
lemma weakRoofDescentProjection_trivialKanFibration {R Q E Z : SSet.{u}} [KanComplex Z]
    {w : R ⟶ Q} (hw : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence w) (i : Z ⟶ E) (t : R ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (weakRoofDescentProjection w i t) := by
  have := (hw.precompose_kan Z).isQCatEquivalence.equivalencePathReplacementMap_trivialKanFibration
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

/-- 二つの比較が弱同値なら、二段降下の空間は全境界を充填する。 -/
theorem weakRoofDescentSpace_isContractibleKan {R Q E Z : SSet.{u}} [KanComplex Z]
    {w : R ⟶ Q} {i : Z ⟶ E} (hw : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence w)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence i) (t : R ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (weakRoofDescentSpace w i t) := by
  have := weakRoofDescentProjection_trivialKanFibration hw i t
  intro n b
  let p := weakRoofDescentProjection w i t
  have := (weakRoofDescentProjection_trivialKanFibration hw i t).mem
    (boundary n).ι inferInstance
  obtain ⟨d, hd⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakHomotopyExtensionSpace_isContractibleKan hi (𝟙 Z) n (b ≫ p)
  have sq : CommSq b (boundary n).ι p d := ⟨hd.symm⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 全空間上で動く、評価側の実際の写像の族。 -/
def weakRoofDescentEvaluation {R Q E Z : SSet.{u}} (w : R ⟶ Q) (i : Z ⟶ E) (t : R ⟶ E) :
    weakRoofDescentSpace w i t ⟶ (ihom E).obj Z :=
  weakRoofDescentProjection w i t ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakHomotopyExtensionEvaluation i (𝟙 Z)

/-- 全空間上で動く、商側の実際の写像の族。 -/
def weakRoofDescentExtension {R Q E Z : SSet.{u}} (w : R ⟶ Q) (i : Z ⟶ E) (t : R ⟶ E) :
    weakRoofDescentSpace w i t ⟶ (ihom Q).obj Z :=
  pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection ((pre w).app Z)

/-- 評価の族は、固定 Hom 上で恒等写像の coherent な比較を持つ。 -/
def weakRoofDescentEvaluationIso {R Q E Z : SSet.{u}} [KanComplex Z]
    (w : R ⟶ Q) (i : Z ⟶ E) (t : R ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (weakRoofDescentEvaluation w i t ≫ (pre i).app Z)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 Z))) := by
  simpa only [weakRoofDescentEvaluation, Category.assoc, SSet.comp_const] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakHomotopyExtensionEvaluationIso i (𝟙 Z))
      (weakRoofDescentProjection w i t)

/-- 商への降下の族は、元の屋根全体で評価の族と coherent に比較される。 -/
def weakRoofDescentExtensionIso {R Q E Z : SSet.{u}} [KanComplex Z]
    (w : R ⟶ Q) (i : Z ⟶ E) (t : R ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (weakRoofDescentExtension w i t ≫ (pre w).app Z)
      (weakRoofDescentEvaluation w i t ≫ (pre t).app Z) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementFunctorIso ((pre w).app Z))
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap ((pre w).app Z))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakHomotopyExtensionEvaluation i (𝟙 Z) ≫ (pre t).app Z))
  rw [← Category.assoc, pullback.condition] at h
  simpa only [weakRoofDescentEvaluation, weakRoofDescentExtension,
    weakRoofDescentProjection, Category.assoc] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
