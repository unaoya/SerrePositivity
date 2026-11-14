module

public import SerrePositivity.EInfinity.BarrattEccles.CAlgDiscreteEmbedding
public import SerrePositivity.EInfinity.ComplexLimits.DerivedNatTransIso
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitProbeFunctor

/-!
# U と元の非置換の通常忘却の全関手比較

概要：同じ cofibrant 置換の元の augmentation を D(R) で反転し、全源を比較する。
方針：元の全自然変換の円柱と、全成分の準同型反転を使う。
規約：元の全代数・離散入力・同じ実忘却 U を保持する。
使われ方：離散入力の既存 D(R) 埋め込みとの全比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma algebraCAlgReplacementNerve_forget :
    algebraCAlgReplacementNerve A ≫ cofibrantAlgebraForgetNerve A =
      nerveMap (framedLimitProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  change (Γ ⋙ cofibrantAlgebraDKReplacement A) ⋙
    (cofibrantAlgebraDKInclusion A ⋙ Operad.Algebra.forget (operad A)) = _
  rw [Functor.assoc, ← Functor.assoc (cofibrantAlgebraDKReplacement A),
    cofibrantAlgebraDKReplacement_comp_inclusion]
  rfl

def algebraUnderlyingDerivedSource : nerve (operad A).Algebra ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  nerveMap (Operad.Algebra.forget (operad A)) ≫ ComplexLimits.complexOrdinaryDerivedSource A

def algebraReplacementUnderlyingDerivedIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (algebraCAlgReplacementNerve A ≫ cofibrantAlgebraUnderlyingDerivedSource A)
      (algebraUnderlyingDerivedSource A) := by
  let η := Functor.whiskerRight (framedLimitProbeComparisonNatTrans A)
    (Operad.Algebra.forget (operad A))
  have hη (X : (operad A).Algebra) : QuasiIso (η.app X) :=
    framedLimitProbeComparison_quasiIso A X
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (nerveMap (framedLimitProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) ≫
        ComplexLimits.complexOrdinaryDerivedSource A) (algebraUnderlyingDerivedSource A) := by
    simpa only [Functor.id_comp, algebraUnderlyingDerivedSource] using
      ComplexLimits.complexOrdinaryDerivedNatTransIso A η hη
  have he : algebraCAlgReplacementNerve A ≫ cofibrantAlgebraUnderlyingDerivedSource A =
      nerveMap (framedLimitProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) ≫
        ComplexLimits.complexOrdinaryDerivedSource A := by
    rw [cofibrantAlgebraUnderlyingDerivedSource, ← Category.assoc,
      algebraCAlgReplacementNerve_forget]
  exact eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) he) ≪≫ e

def algebraCAlgSource_underlyingDerivedIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (algebraCAlgSource A ≫ cAlgForgetDerived A) (algebraUnderlyingDerivedSource A) :=
  algebraCAlgSource_forgetIso A ≪≫ algebraReplacementUnderlyingDerivedIso A

def discreteCAlgEmbedding_underlyingDerivedIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (discreteCAlgEmbedding A ≫ cAlgForgetDerived A)
      (nerveMap (discreteAlgebraFunctor A) ≫ algebraUnderlyingDerivedSource A) := by
  simpa only [discreteCAlgEmbedding, Category.assoc] using
    (algebraCAlgSource_underlyingDerivedIso A).precomp (nerveMap (discreteAlgebraFunctor A))

end SerrePositivity.EInfinity.BarrattEccles
