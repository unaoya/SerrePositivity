module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.StableQuotientTriangle
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseAscent
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseMorphismUp

/-!
概要：固定商射と別の懸垂模型の射との比較を、cone 上の比較三角形から回収する。
方針：実局所化の宇宙絶対性を使い、大きい標的への全前合成の充満忠実性で反映する。
規約：別模型の存在・比較同値・入力全体の高次整合は仮定から生成しない。
使われ方：Calkin 商・その冪等完備化の射と、同じ固定 Q(data) を照合する接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory DifferentialGraded KST.NonConnective SSet MonoidalClosed
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (A B : Type v)
  [DGCategory R A] [Small.{u} A] [DGCategory R B] [Small.{u} B]
  {κ : Cardinal.{u}} (IA : DGKappaConeInput R A κ) (IB : DGKappaConeInput R B κ)
  (d : DGKappaSuspensionMapData R A B IA IB)

/-- 同じ商射の全前合成は、Calkin／Idem の大きい宇宙の標的でも充満忠実。 -/
theorem dgSuspensionQuotientLiftedPrecomposition_isFullyFaithful
    (Y : SSet.{max (max (u + 1) v) w}) [Quasicategory Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre ((SSet.uliftFunctor.{w, max (u + 1) v}).map
      (dgKappaSuspensionProjection R A IA))).app Y) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_isLocalization R (DGKappaCone R A IA)
    (dgKappaConePerfectObjects R A IA)).precomposition_isFullyFaithful_ulift Y

/-- 固定された三角形をそのまま宇宙持ち上げする。商射や逆比較を選び直さない。 -/
def dgSuspensionQuotientLiftedTriangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{w, max (u + 1) v}).map
      (dgKappaSuspensionProjection R A IA) ≫
      (SSet.uliftFunctor.{w, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaSuspensionInputMap R A B IA IB d).down))
      ((SSet.uliftFunctor.{w, max (u + 1) v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map d.cone) ≫
      (SSet.uliftFunctor.{w, max (u + 1) v}).map (dgKappaSuspensionProjection R B IB)) := by
  simpa only [Functor.map_comp] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.functorIso_ulift.{max (u + 1) v, w}
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionQuotientTriangle R A B IA IB d))

variable {X Y : SSet.{max (max (u + 1) v) w}} [Quasicategory X] [Quasicategory Y]
  (a : (SSet.uliftFunctor.{w, max (u + 1) v}).obj (dgKappaSuspensionInfinity R A IA) ⟶ X)
  (b : (SSet.uliftFunctor.{w, max (u + 1) v}).obj
    (dgKappaSuspensionInfinity R B IB) ⟶ Y) (G : X ⟶ Y)

/-- 比較三角形が供給された別模型の射と、固定商射との自然性四角形。
a・b は同値でなくてもよく、特に完備化への射にも適用できる。 -/
def dgSuspensionQuotientModelComparison
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{w, max (u + 1) v}).map
      (dgKappaSuspensionProjection R A IA) ≫
      a ≫ G) ((SSet.uliftFunctor.{w, max (u + 1) v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map d.cone) ≫
      (SSet.uliftFunctor.{w, max (u + 1) v}).map
      (dgKappaSuspensionProjection R B IB) ≫
      b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{w, max (u + 1) v}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaSuspensionInputMap R A B IA IB d).down) ≫
      b) (a ≫ G) := by
  apply (dgSuspensionQuotientLiftedPrecomposition_isFullyFaithful.{u, v, w}
    R A IA Y).preimageVertexIso
  have h := (dgSuspensionQuotientLiftedTriangle.{u, v, w} R A B IA IB d).postcomp b
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((SSet.uliftFunctor.{w, max (u + 1) v}).map
      (dgKappaSuspensionProjection R A IA) ≫
      ((SSet.uliftFunctor.{w, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaSuspensionInputMap R A B IA IB d).down) ≫ b))
    ((SSet.uliftFunctor.{w, max (u + 1) v}).map
      (dgKappaSuspensionProjection R A IA) ≫
      (a ≫ G))
  simpa only [Category.assoc] using h ≪≫ hG.symm

/-- cone 模型・射影・cone 射の比較を貼り合わせ、必要な商の三角形を作る。
これにより、新 Σ∞ の射の照合に残る供給を cone 側の三つの比較へ分離する。 -/
def dgSuspensionQuotientConeModelComparison
    {CA CB : SSet.{max (max (u + 1) v) w}}
    (cA : (SSet.uliftFunctor.{w, max (u + 1) v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R A IA)) ⟶ CA)
    (cB : (SSet.uliftFunctor.{w, max (u + 1) v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R B IB)) ⟶ CB)
    (pA : CA ⟶ X) (pB : CB ⟶ Y) (L : CA ⟶ CB)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{w, max (u + 1) v}).map
      (dgKappaSuspensionProjection R A IA) ≫
      a) (cA ≫ pA))
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{w, max (u + 1) v}).map
      (dgKappaSuspensionProjection R B IB) ≫
      b) (cB ≫ pB))
    (hcone : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{w, max (u + 1) v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map d.cone) ≫
      cB) (cA ≫ L))
    (hdescent : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (pA ≫ G) (L ≫ pB)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{w, max (u + 1) v}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaSuspensionInputMap R A B IA IB d).down) ≫
      b) (a ≫ G) := by
  apply dgSuspensionQuotientModelComparison R A B IA IB d a b G
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{w, max (u + 1) v}).map
      (dgKappaSuspensionProjection R A IA) ≫
      a ≫ G) (cA ≫ pA ≫ G) := by
    simpa only [Category.assoc] using hA.postcomp G
  have h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cA ≫ pA ≫ G) (cA ≫ L ≫ pB) :=
    hdescent.precomp cA
  have h₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cA ≫ L ≫ pB)
      ((SSet.uliftFunctor.{w, max (u + 1) v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map d.cone) ≫
      cB ≫ pB) := by
    simpa only [Category.assoc] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp hcone.symm pB
  have h₄ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{w, max (u + 1) v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map d.cone) ≫
      cB ≫ pB) ((SSet.uliftFunctor.{w, max (u + 1) v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map d.cone) ≫
      (SSet.uliftFunctor.{w, max (u + 1) v}).map
      (dgKappaSuspensionProjection R B IB) ≫
      b) :=
    (hB.precomp ((SSet.uliftFunctor.{w, max (u + 1) v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map d.cone))).symm
  exact h₁ ≪≫ h₂ ≪≫ h₃ ≪≫ h₄

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
