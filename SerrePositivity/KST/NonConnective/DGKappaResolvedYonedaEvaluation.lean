module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedKernelYoneda
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGKernelTensorYonedaNerveIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedRawFactor

/-!
概要：同じ実小核の Yoneda 後の実評価 Morita 作用を、元の厳密評価へ比較する。
方針：D 正本の tensor・Yoneda 同型を、同じ入力の半自由比較と実出力分解へ送る。
規約：同じ I に条件付きで、元の評価核と元の実 Perf 作用を変えない。
使われ方：K-7 c5 の実評価・元の P 包含の全関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
local notation "C" => dgKappaResolvedKernelKInput R D I

/-- 概要：同じ実小核の元の Yoneda 後の tensor は、元の実評価と全関手で同型。
方針：D 正本の全 Hom 自然な右単位を、同じ核の対象ラベルの移送前へ戻す。
規約：同じ実評価双加群と元の全単体を保持する。
使われ方：実出力分解を通す前の c5 の比較。 -/
def dgKappaResolvedYonedaTensorIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (C)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R (C) Set.univ) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R (C) D (dgKappaResolvedEvaluationBimodule R D I)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedEvaluationBimodule R D I)) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorYonedaCompositeIso R (C) D
    (dgKappaResolvedEvaluationBimodule R D I)).precomp
      (dgKappaResolvedKernelLiftIso R D I).hom
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity_inclusion R (C)] at e
  simp only [← Category.assoc, dgKappaResolvedKernelYoneda_lift] at e
  have he : (dgKappaResolvedKernelLiftIso R D I).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R (C)).comp
        (dgKappaResolvedEvaluationBimodule R D I)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedEvaluationBimodule R D I) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (C)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map _ = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
    congr 1
  rw [he] at e
  simpa only [Category.assoc] using! e

/-- 概要：同じ実小核の Yoneda の半自由包含は、元の代表加群の全族を回収する。
方針：同じ射影的模型同値の逆二胞体を、元の Yoneda と生の加群包含で挟む。
規約：同じ核上の元の Yoneda に限る。新たな分解や代表選択を加えない。
使われ方：元の実 kernel 作用へ tensor・Yoneda 比較を代入する。 -/
def dgKappaResolvedYonedaInclusionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (C)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R (C) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R (C))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R (C))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (C)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R (C) Set.univ)) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R (C)).choose
  let J := dgFullSubcategoryInclusion R (RightModule R (C))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R (C))
  have h := (e.invHomIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J)).precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (C)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R (C)))
  simpa only [e, J, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
    Category.comp_id] using! h

/-- 概要：同じ実核の元の Yoneda 後の実 kernel 作用は、元の実評価の分解と全関手で同型。
方針：同じ半自由包含の回収と tensor・Yoneda 同型を実出力分解へ送る。
規約：元の実評価核を保持し、対象別の代表同型で代用しない。
使われ方：元の実 Perf 作用と厳密評価の比較を導来模型で検証する。 -/
def dgKappaResolvedYonedaKernelIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (C)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R (C) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (C) D
        (dgKappaResolvedEvaluationBimodule R D I))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (C) D (dgKappaResolvedEvaluationBimodule R D I)) := by
  let T := Morita.kernelTensor R (C) D (dgKappaResolvedEvaluationBimodule R D I)
  let J := dgFullSubcategoryInclusion R (RightModule R (C))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R (C))
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R D) D (DGFunctor.id (RightModule R D))
  have hK := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R (C)) D
    (J.comp T)).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (C)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R (C))
  have hJ := (dgKappaResolvedYonedaInclusionIso R D I).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map T ≫ L)
  have hT := (dgKappaResolvedYonedaTensorIso R D I).postcomp L
  have hE := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (C) D
    (dgKappaResolvedEvaluationBimodule R D I)).symm
  have hK' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (C)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R (C) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (C) D
        (dgKappaResolvedEvaluationBimodule R D I))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (C)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R (C) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map T ≫ L)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG,
      J, T, L, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc] using! hK
  exact hK' ≪≫ hJ ≪≫ (by simpa only [Category.assoc] using! hT) ≪≫ hE

/-- 概要：元の実 Perf Morita 作用と元の厳密評価は、同じ実核の Yoneda 上で全関手同型。
方針：両作用の元の導来包含比較をつなぎ、その同じ充満忠実な包含から反映する。
規約：同じ I に条件付き。独立の P は D の実供給で置き換える。
使われ方：c5 の実評価 Morita 比較と元の P の包含の照合。 -/
def dgKappaResolvedYonedaPerfectIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (C)) ≫
      dgKappaResolvedPerfectInfinity R D I (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedPerfectEvaluation R D I (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I))) := by
  have hP := (dgKappaResolvedPerfectInfinity_inclusionIso R D I
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I)).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (C)))
  have hK := dgKappaResolvedYonedaKernelIso R D I
  have hE := (dgKappaResolvedPerfectEvaluation_resolvedIso R D I
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I)).symm
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity_isFullyFaithful R D).preimageFunctorIso
  simpa only [Category.assoc] using! hP ≪≫ hK ≪≫ hE

/-- 概要：元の P の比較を同じ実核の Yoneda に続けると、元の実 Perf 作用の逆となる。
方針：構成済みの全 Yoneda 評価比較を P に制限し、元の評価との逆二胞体を保持する。
規約：同じ I と任意の既存 P に条件付き。実 Perf 作用は D の標準 P で固定する。
使われ方：元の P の包含と元の Morita 逆作用の全関手照合。 -/
def dgKappaResolvedYonedaPerfectComparison_counit (P : DGKappaPerfectInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((dgKappaPerfectResolvedComparison R D I P ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (C))) ≫
      dgKappaResolvedPerfectInfinity R D I (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R D)) := by
  have h := (dgKappaResolvedYonedaPerfectIso R D I).precomp
    (dgKappaPerfectResolvedComparison R D I P)
  have hp := dgKappaPerfectResolvedComparison_evaluationIso R D I P
  rw [dgKappaResolvedPerfectEvaluation_perfect_input_irrel R D I P
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I)] at hp
  exact (by simpa only [Category.assoc] using! h) ≪≫ hp

/-- 概要：元の P の後の元の Yoneda と、同じ実 Morita 同値の選ばれた逆は全関手で同型。
方針：同じ実 Perf 作用の充満忠実性から元の余単位比較を反映する。
規約：同じ実 Morita 作用の順方向を変更せず、全 native Hom の比較を保持する。
使われ方：K-7 c5 の元の P と実評価 Morita 比較の選択照合。 -/
def dgKappaResolvedYonedaPerfectComparison (P : DGKappaPerfectInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaPerfectResolvedComparison R D I P ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (C)))
      (dgKappaResolvedPerfectInfinity_isQCatEquivalence R D I
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I)).choose.inv := by
  let e := (dgKappaResolvedPerfectInfinity_isQCatEquivalence R D I
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I)).choose
  apply e.isQCatEquivalence.isFullyFaithful.preimageFunctorIso
  exact dgKappaResolvedYonedaPerfectComparison_counit R D I P ≪≫ e.invHomIso.symm

/-- 概要：同じ実 Morita 作用への後合成は、元の指定余単位比較を厳密に回収する。
方針：F1 正本の充満忠実な同型回収の逆則を同じ実作用へ適用する。
規約：同じ P と同じ選択逆二胞体を保持する。
使われ方：P の包含比較の検証で、別の比較同型への置換を避ける。 -/
theorem dgKappaResolvedYonedaPerfectComparison_postcomp (P : DGKappaPerfectInput R D I) :
    (dgKappaResolvedYonedaPerfectComparison R D I P).postcomp
      (dgKappaResolvedPerfectInfinity R D I (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I)) =
      dgKappaResolvedYonedaPerfectComparison_counit R D I P ≪≫
        (dgKappaResolvedPerfectInfinity_isQCatEquivalence R D I
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I)).choose.invHomIso.symm := by
  exact (dgKappaResolvedPerfectInfinity_isQCatEquivalence R D I
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I)).isFullyFaithful.preimageFunctorIso_postcomp _

/-- 概要：元の P と Yoneda の比較は、固定 ν の元の実評価 Perf 同値へ全関手で戻る。
方針：同じ二つのラベル評価同値で構成済みの実 Morita 逆比較を挟む。
規約：固定 ν・元のラベル評価・既存の実 Perf 同値を変更しない。
使われ方：K-7 c5 の元の P と固定 ν の実 Perf 同値の照合。 -/
def dgKappaResolvedYonedaFixedPerfComparison (P : DGKappaPerfectInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((presentedPerfectDGQCatEvaluationEquivalence R D).hom ≫
        dgKappaPerfectResolvedComparison R D I P ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (C)) ≫
        (presentedPerfectDGQCatEvaluationEquivalence R (C)).inv)
      (dgKappaResolvedKernelPerfEquivalence R D I P).hom.val := by
  have h := ((dgKappaResolvedYonedaPerfectComparison R D I P).precomp
    (presentedPerfectDGQCatEvaluationEquivalence R D).hom).postcomp
      (presentedPerfectDGQCatEvaluationEquivalence R (C)).inv
  simpa only [dgKappaResolvedKernelPerfEquivalence, dgKappaResolvedKernelPerfQCatEquivalence,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.symm, Category.assoc] using! h

end SerrePositivity.KST.NonConnective
