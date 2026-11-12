module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCompletion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectYoneda
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift

/-!
概要：実完備化射を同じ Perf 評価で戻すと元 resolved 商の Yoneda を回収する。
方針：指定評価同値の単位二胞体を保持し、対象宇宙の上げ下げを厳密に消去する。
規約：完備化射を任意の存在証人へ置換しない。
使われ方：固定 ν の商辺と native resolved 射影の完備化の自然性比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local notation "Q" => DGQuotient.QuotientObject
  (DGCategoryCellResolution.Source R (DGOdotGluing R d))
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))

/-- 概要：同じ終域評価の逆を消すと指定した共通宇宙 Yoneda が戻る。
方針：構成した評価同値の同じ単位二胞体で戻す。規約：全関手同型を保持する。
使われ方：実 c の具体的な作用の照合。 -/
def dgOdotMilnorCompletionValueComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorCompletion R d).hom ≫
      (dgOdotMilnorResolvedPerfectValueEquivalence R d).inv)
    ((dgOdotMilnorResolvedLiftEquivalence R d).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity R (Q)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (((dgOdotMilnorResolvedLiftEquivalence R d).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity R (Q) ≫
        (dgOdotMilnorResolvedPerfectValueEquivalence R d).hom)) ≫
          (dgOdotMilnorResolvedPerfectValueEquivalence R d).inv) _
  simpa only [Category.assoc, Category.comp_id] using
    ((dgOdotMilnorResolvedPerfectValueEquivalence R d).homInvIso.precomp
      ((dgOdotMilnorResolvedLiftEquivalence R d).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity R (Q)))

/-- 概要：同じ native 商から共通宇宙を経由した Yoneda は元の実 Yoneda と厳密一致。
方針：対象宇宙の上げ下げを元の dg 関手上で消去する。規約：全単体の等号。
使われ方：完備化射の評価後の実 Yoneda 回収。 -/
lemma dgOdotMilnorCompletion_lift_yoneda :
    (dgOdotMilnorResolvedLiftEquivalence R d).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity R (Q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (Q)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, u + 1} R (Q)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R (Q)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (Q))) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  congr 1

/-- 概要：実 c を同じ評価で戻すと元商の Yoneda になる。
方針：構成した指定全関手同型の終点を厳密回収式で照合する。
規約：対象別の比較に弱めない。使われ方：resolved 商辺の固定 ν 自然性。 -/
def dgOdotMilnorCompletionYonedaComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorCompletion R d).hom ≫
      (dgOdotMilnorResolvedPerfectValueEquivalence R d).inv)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (Q))) := by
  have e := dgOdotMilnorCompletionValueComparison R d
  rw [dgOdotMilnorCompletion_lift_yoneda] at e
  exact e

/-- 概要：元の resolved 射影の完備化も同じ評価後に元の Yoneda 合成へ戻る。
方針：構成した同じ評価比較を元の射影で前合成する。
規約：元の native 商射影を保持する。使われ方：固定 ν の商辺との照合。 -/
def dgOdotMilnorProjectionYonedaComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom ≫
      ((dgOdotMilnorCompletion R d).hom ≫
        (dgOdotMilnorResolvedPerfectValueEquivalence R d).inv))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (Q))) :=
  (dgOdotMilnorCompletionYonedaComparison R d).precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom

end SerrePositivity.KST.SConstruction
