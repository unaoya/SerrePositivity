module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.FixedSimplicialModelCompatibility
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenMapComparison
public import SerrePositivity.HomotopicalAlgebra.Quillen.CofibrantObjects
public import SerrePositivity.HomotopicalAlgebra.Quillen.FibrantCriterion

/-!
概要：simplicial Quillen 対応の混合 Hom に対する、元の cf 置換からの trivial Kan 比較。
方針：右像の cofibrant 置換の fibrancy と左像の fibrant 置換の cofibrancy を導き、固定 SM7 を使う。
規約：置換は元の因子分解の射そのもの。使われ方：HTT 5.2.4.6 の Cartesian・coCartesian 射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u vC vD
open CategoryTheory Limits HomotopicalAlgebra SSet
open SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section
variable {C : Type vC} [Category.{u} C] [ModelCategory C]
  {D : Type vD} [Category.{u} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [SerrePositivity.Quillen.IsLeftQuillen L]
  (cofC : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fibD : MorphismProperty.FunctorialFactorizationData (trivialCofibrations D) (fibrations D))

include adj in
/-- 元の fibrant 右像の cofibrant 置換も fibrant であり、同じ対象が cf になる。 -/
lemma quillenRightReplacement_isFibrant (Y : D) [IsFibrant Y] :
    IsFibrant ((cofibrantSource cofC).obj (R.obj Y)) := by
  have := adj.isRightAdjoint
  have := SerrePositivity.Quillen.isRightQuillen_of_isLeftQuillen adj
  have hf := SerrePositivity.Quillen.isFibrant_obj R Y
  have : IsFibrant ((𝟭 C).obj (R.obj Y)) := hf
  have : Fibration ((cofibrantSourceComparison cofC).app (R.obj Y)) :=
    ⟨(cofibrantSourceComparison_trivialFibration cofC (R.obj Y)).1⟩
  exact isFibrant_of_fibration ((cofibrantSourceComparison cofC).app (R.obj Y))

include adj in
/-- 元の cofibrant 左像の fibrant 置換も cofibrant であり、同じ対象が cf になる。 -/
lemma quillenLeftReplacement_isCofibrant (X : C) [IsCofibrant X] :
    IsCofibrant ((fibrantTarget fibD).obj (L.obj X)) := by
  have := adj.isLeftAdjoint
  have hc := SerrePositivity.Quillen.isCofibrant_obj L X
  have : IsCofibrant ((𝟭 D).obj (L.obj X)) := hc
  have : Cofibration ((fibrantTargetComparison fibD).app (L.obj X)) :=
    ⟨(fibD.hi (Arrow.mk (terminal.from (L.obj X)))).1⟩
  exact isCofibrant_of_cofibration ((fibrantTargetComparison fibD).app (L.obj X))

variable [EnrichedOrdinaryCategory SSet.{u} C]
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SC.tensor]

omit [ModelCategory D] in
include SC in
/-- 元の右置換射を混合 Hom へ後合成した射そのものが trivial Kan fibration である。 -/
lemma quillenRightReplacementHom_trivialKanFibration (X : C) [IsCofibrant X] (Y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
      (eHomWhiskerLeft SSet.{u} X ((cofibrantSourceComparison cofC).app (R.obj Y))) := by
  have hp := cofibrantSourceComparison_trivialFibration cofC (R.obj Y)
  have : Fibration ((cofibrantSourceComparison cofC).app (R.obj Y)) := ⟨hp.1⟩
  have : WeakEquivalence ((cofibrantSourceComparison cofC).app (R.obj Y)) := ⟨hp.2⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedEnrichedHom_trivialKanFibration SC X _

include adj SC in
/-- 元の cofibrant 始域と fibrant な右段対象の混合 Hom は Kan である。 -/
lemma quillenMixedHom_kanComplex (X : C) [IsCofibrant X] (Y : D) [IsFibrant Y] :
    KanComplex (X ⟶[SSet.{u}] R.obj Y) := by
  have := adj.isRightAdjoint
  have := SerrePositivity.Quillen.isRightQuillen_of_isLeftQuillen adj
  have := SerrePositivity.Quillen.isFibrant_obj R Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedEnrichedHom_kanComplex SC X (R.obj Y)

variable [EnrichedOrdinaryCategory SSet.{u} D]
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SD.tensor]

omit [ModelCategory C] [SerrePositivity.Quillen.IsLeftQuillen L]
  [EnrichedOrdinaryCategory SSet.{u} C] in
include SD in
/-- 元の左置換射による混合 Hom への前合成も、その同じ射で trivial Kan fibration。 -/
lemma quillenLeftReplacementHom_trivialKanFibration (X : C) (Y : D) [IsFibrant Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
      (eHomWhiskerRight SSet.{u} ((fibrantTargetComparison fibD).app (L.obj X)) Y) := by
  have hp := fibD.hi (Arrow.mk (terminal.from (L.obj X)))
  have : Cofibration ((fibrantTargetComparison fibD).app (L.obj X)) := ⟨hp.1⟩
  have : WeakEquivalence ((fibrantTargetComparison fibD).app (L.obj X)) := ⟨hp.2⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedEnrichedHom_sourceTrivialKanFibration SD _ Y

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
