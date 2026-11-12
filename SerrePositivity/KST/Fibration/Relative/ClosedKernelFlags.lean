module
public import SerrePositivity.KST.Fibration.Relative.ClosedFlagConstants
public import SerrePositivity.KST.Fibration.WeakStringPostNaturality
public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps
public import SerrePositivity.KST.Comparison.SegalRealizationComparison

/-!
概要：P 内の全旗 E_P と元の W 旗への包含。
方針：零圏への関手の全旗模型を使用し、包含の実 cofiber 保存で W 所属を示す。
規約：零圏は P 内の全旗を表すためだけに使う。使われ方：Prop 値の自然性条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：P の同じ模型から零圏への完全射。
方針：既存の零圏射。規約：商射ではない。使われ方：全旗の表現。 -/
def closedKernelZeroMap {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (flagAmbient (closedStableModel P)) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (flagAmbient (closedStableModel P))

/-- 概要：零圏への W 条件は全旗で自動的。
方針：全 cofiber の像は零。規約：P の対象を制限しない。
使われ方：E_P が全 Fun であることの保証。 -/
lemma closedKernelFlag_all {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory)
    (v : ((ihom (stdSimplex.obj n)).obj (closedStableModel P).carrier) _⦋0⦌) :
    weakStringPredicate (closedKernelZeroMap P) n v := by
  unfold weakStringPredicate
  intro α
  exact isIso_of_isTerminal (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _).2.isTerminalHo
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _).2.isTerminalHo _

/-- 概要：P の包含の同じ完全射。
方針：保存データを既存の ExactMap に包装。
規約：底の射は元の包含。使われ方：全図式の後合成。 -/
def closedKernelInclusion {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (flagAmbient (closedStableModel P)) (flagAmbient B) where
  hom := (closedStableInclusion P).val
  isExact := (closedStableInclusion P).property.isExactFunctor

/-- 概要：P 内の全ての辺は B の元の W 辺へ写る。
方針：P 内の実 cofiber を完全包含で写す。
規約：retract 閉包なし。使われ方：全旗包含の所属証明。 -/
lemma closedKernel_edge_mem {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (a : (closedStableModel P).carrier _⦋1⦌) :
    (closedStableInclusion P).val.app _ a ∈ closedStableEdges P := by
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a)
  have h := (closedStableEdges_iff_cofiber P (s.map (closedKernelInclusion P).hom)).2
    (closedSubcategory_vertex P s.cofiber)
  exact h

/-- 概要：P の任意の全旗は元の W 全旗に入る。
方針：全辺で同じ cofiber 判定を適用。
規約：全合成辺と退化辺。使われ方：包含の全部分圏への持ち上げ。 -/
lemma closedKernel_post_mem {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory)
    (v : ((ihom (stdSimplex.obj n)).obj (closedStableModel P).carrier) _⦋0⦌) :
    (closedFlagStablePredicate P n).predicate
      (((ihom (stdSimplex.obj n)).map (closedStableInclusion P).val).app _ v) := by
  apply (closedFlagStablePredicate_iff P n _).2
  unfold closedFlagPredicate
  change simplexVertexValue n
    (((ihom (stdSimplex.obj n)).map (closedKernelInclusion P).hom).app _ v) ∈ _
  rw [simplexVertexValue_postcomp (closedKernelInclusion P)]
  intro α
  have h := NatTrans.naturality_apply (closedStableInclusion P).val α.op
    (simplexVertexValue n v)
  exact (congrArg (· ∈ closedStableEdges P) h).mp (closedKernel_edge_mem P _)

/-- 概要：元の P 全旗から元の W 全旗への完全包含。
方針：実後合成を全部分圏へ制限。
規約：全自然変換。使われ方：自然性の明示仮定の各成分。 -/
def closedKernelFlagPost {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory) : weakStringModel (closedKernelZeroMap P) n ⟶ closedFlagModel P n :=
  ⟨fullPredicateMap ((ihom (stdSimplex.obj n)).map (closedStableInclusion P).val)
      (weakStringPredicate (closedKernelZeroMap P) n) (closedFlagStablePredicate P n).predicate
      (fun v _ => closedKernel_post_mem P n v), by
    apply preservesCofiberData_fullSubcomplex_of_comp
      (closedFlagStablePredicate P n).predicate
    rw [fullPredicateMap_ι]
    exact (closedStableInclusion
      (weakStringClosedPredicate (closedKernelZeroMap P) n)).property.comp
      (exactMap_preservesSData (exactFunctorMap (stdSimplex.obj n)
        (closedKernelInclusion P))).toCofiberData⟩

/-- 概要：全旗の包含後は元の後合成。
方針：全部分圏の普遍公式。規約：厳密等号。使われ方：自然性の計算。 -/
lemma closedKernelFlagPost_inclusion {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory) : (closedKernelFlagPost P n).val ≫
      (closedStableInclusion (closedFlagStablePredicate P n)).val =
      (closedStableInclusion (weakStringClosedPredicate (closedKernelZeroMap P) n)).val ≫
        (ihom (stdSimplex.obj n)).map (closedStableInclusion P).val :=
  fullPredicateMap_ι _ _ _ (fun v _ => closedKernel_post_mem P n v)

/-- 概要：同じ後合成は全ての面・退化と可換。
方針：元の周囲の前合成・後合成の可換条件。
規約：全単体作用素。使われ方：明示仮定の自然変換。 -/
lemma closedKernelFlagPost_reindex {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    weakStringExactMap (closedKernelZeroMap P) θ ≫ closedKernelFlagPost P m =
      closedKernelFlagPost P n ≫ closedFlagMap P θ := by
  apply Subtype.ext
  apply SSet.hom_ext
  intro k
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app ((pre (stdSimplex.map θ)).naturality
      (closedStableInclusion P).val) k) x.val

/-- 概要：E_P の core S 実現図式。
方針：全旗の零圏模型へ F を適用。規約：全次数。使われ方：収縮する底。 -/
def closedKernelFlagDiagram {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    SimplicialObject SSet.{u} := weakStringStableSimplicial (closedKernelZeroMap P) ⋙
      coreSRealizationFunctor

/-- 概要：同じ元の包含を全単体的に束ねる。
方針：上の厳密自然性に F を適用。規約：商なし。
使われ方：K-B の有限旗自然性供給を受ける境界。 -/
def closedStableFlagPost {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    closedKernelFlagDiagram P ⟶ closedFlagRealizationDiagram P where
  app n := coreSRealizationFunctor.map (closedKernelFlagPost P n.unop)
  naturality {_ _} θ := by
    change coreSRealizationFunctor.map (weakStringExactMap (closedKernelZeroMap P) θ.unop) ≫
      coreSRealizationFunctor.map (closedKernelFlagPost P _) =
        coreSRealizationFunctor.map (closedKernelFlagPost P _) ≫
          coreSRealizationFunctor.map (closedFlagMap P θ.unop)
    rw [← coreSRealizationFunctor.map_comp, ← coreSRealizationFunctor.map_comp]
    exact congrArg coreSRealizationFunctor.map (closedKernelFlagPost_reindex P θ.unop)

/-- 概要：未受領の有限旗自然性供給を表す命題。
方針：元の SSet 自然性四角形の全作用素の条件をそのまま要求する。
規約：公理・instance として導入しない。使われ方：後段定理の明示引数。 -/
def ClosedStableFlagPostPullback {B : StableModel.{u}} (P : ClosedStablePredicate B) : Prop :=
  ∀ {m n : SimplexCategory} (θ : m ⟶ n),
    IsHomotopyPullback (CommSq.mk ((closedStableFlagPost P).naturality θ.op))

end SerrePositivity.KST.Fibration.Relative
