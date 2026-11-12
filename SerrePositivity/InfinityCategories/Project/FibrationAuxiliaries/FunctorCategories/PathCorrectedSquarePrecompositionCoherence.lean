module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedSquareExactIso
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoPrecompositionProjection

/-!
概要：補正成分の同じ指定同型は、前合成後も元の自然性を厳密に回収する。
方針：端点表示の変更を除いた像の等式と前後合成の交換を使う。
規約：持ち上げた同じ path の同型を保持する。
使われ方：元の全 Hom 上の補正成分の共有頂点での整合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 始点表示の等式から来る同型を外すと、元の指定値を回収する。 -/
lemma functorIsoOfEq_eq_of_eqToIso_trans {A B : SSet.{u}}
    {f f' g : A ⟶ B} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g) (h : f = f')
    (hc : c = eqToIso (congrArg
      (fun m ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex m)) h) ≪≫ e) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq c h rfl = e := by
  subst f'
  have hh : c = e := by simpa only [eqToIso_refl, Iso.refl_trans] using hc
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq c rfl rfl).trans (heq_of_eq hh))

/-- 補正成分の指定像を同じ始点表示へ移すと、元の指定自然性そのもの。 -/
lemma PathCorrectedFunctorSquare.exactComponentIso_postcomp_normalized
    {A E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    {q : E ⟶ B} {f : A ⟶ E} {g : A ⟶ B} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (f ≫ q)}
    (s : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare q f g e) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (s.exactComponentIso.postcomp q) s.comm rfl = e :=
  functorIsoOfEq_eq_of_eqToIso_trans _ e s.comm s.exactComponentIso_postcomp

/-- 同じ補正成分の像は、元の作用で前合成しても同じ指定自然性を回収する。 -/
lemma PathCorrectedFunctorSquare.exactComponentIso_precomp_postcomp_heq
    {H A E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    {q : E ⟶ B} {f : A ⟶ E} {g : A ⟶ B} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (f ≫ q)}
    (s : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare q f g e) (r : H ⟶ A) :
    HEq ((s.exactComponentIso.precomp r).postcomp q) (e.precomp r) := by
  have hn := congrArg (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp v r)
    s.exactComponentIso_postcomp_normalized
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp s.exactComponentIso r q)).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_precomp_heq (s.exactComponentIso.postcomp q) s.comm rfl r).symm.trans
      (heq_of_eq hn))

/-- 同じ補正成分の共有頂点への像の始点は、元の自然性の始点。 -/
lemma PathCorrectedFunctorSquare.exactComponentIso_precomp_postcomp_source
    {H A E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    {q : E ⟶ B} {f : A ⟶ E} {g : A ⟶ B} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (f ≫ q)}
    (s : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare q f g e) (r : H ⟶ A) :
    (r ≫ s.map) ≫ q = r ≫ g :=
  (Category.assoc _ _ _).trans (congrArg (fun m ↦ r ≫ m) s.comm)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
