module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionPerfectChoiceCoherence

/-!
概要：同じ Perf 選択比較の恒等・合成を、固定 ν の元のラベル付き値へ移す。
方針：元の評価同値で挟み、中間評価の指定逆二胞体だけを縮約する。
規約：固定 S・ν を変更しない。dg 入力間の全作用や反復構造辺は別工程。
使われ方：K-7 d4 の元の固定 ν 値における選択比較と全パラメータ制限。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I J K : DGKappaConeInput R A κ)
  (P : DGKappaPerfectInput R A I) (Q : DGKappaPerfectInput R A J)
  (T : DGKappaPerfectInput R A K)

/-- 同じ実評価を使った自己選択比較は、固定 ν 値の恒等関手と同型。 -/
def dgKappaSuspensionNuChoice_selfIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaSuspensionNuChoiceEquivalence R A I I P P).hom (𝟙 _) := by
  let a := presentedPerfectDGQCatEvaluationEquivalence R (dgKappaSuspensionKInput R A I)
  have e := ((dgKappaSuspensionPerfectChoice_selfIso R A I P).postcomp a.inv).precomp a.hom
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaSuspensionNuChoiceEquivalence R A I I P P).hom
      (a.hom ≫ a.inv) := by
    simpa only [dgKappaSuspensionNuChoiceEquivalence, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.symm, Category.assoc, Category.id_comp, a] using! e
  exact h ≪≫ a.homInvIso

/-- 中間実評価を縮約した三選択比較は、同じ固定 ν 値の直接比較と同型。 -/
def dgKappaSuspensionNuChoice_compIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((dgKappaSuspensionNuChoiceEquivalence R A I J P Q).hom ≫
      (dgKappaSuspensionNuChoiceEquivalence R A J K Q T).hom)
      (dgKappaSuspensionNuChoiceEquivalence R A I K P T).hom := by
  let a := presentedPerfectDGQCatEvaluationEquivalence R (dgKappaSuspensionKInput R A I)
  let b := presentedPerfectDGQCatEvaluationEquivalence R (dgKappaSuspensionKInput R A J)
  let c := presentedPerfectDGQCatEvaluationEquivalence R (dgKappaSuspensionKInput R A K)
  let F := (dgKappaSuspensionPerfectChoiceEquivalence R A I J P Q).hom
  let G := (dgKappaSuspensionPerfectChoiceEquivalence R A J K Q T).hom
  have e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((a.hom ≫ (F ≫ b.inv)) ≫ (b.hom ≫ (G ≫ c.inv)))
      (a.hom ≫ ((F ≫ G) ≫ c.inv)) := by
    have h := (b.invHomIso.postcomp (G ≫ c.inv)).precomp (a.hom ≫ F)
    simpa only [Category.assoc, Category.id_comp] using! h
  have e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a.hom ≫ ((F ≫ G) ≫ c.inv))
      (a.hom ≫ ((dgKappaSuspensionPerfectChoiceEquivalence R A I K P T).hom ≫ c.inv)) :=
    ((dgKappaSuspensionPerfectChoice_compIso R A I J K P Q T).postcomp c.inv).precomp a.hom
  simpa only [dgKappaSuspensionNuChoiceEquivalence, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.symm, Category.assoc, a, b, c, F, G] using! e₀ ≪≫ e₁

/-- 同じ固定 ν の実全関手比較を、任意高次パラメータへ前合成する。 -/
def dgKappaSuspensionNuChoiceParameterIso {S : SSet.{max (u + 1) v}}
    (a : S ⟶ (dgKInputStableValue R (dgKappaSuspensionKInput R A I)).obj) :=
  (dgKappaSuspensionNuChoice_compIso R A I J K P Q T).precomp a

/-- 元の指定比較は、任意パラメータの再制限でも同じ比較を回収する。 -/
theorem dgKappaSuspensionNuChoiceParameterIso_precomp {S U : SSet.{max (u + 1) v}}
    (a : S ⟶ (dgKInputStableValue R (dgKappaSuspensionKInput R A I)).obj) (r : U ⟶ S) :
    (dgKappaSuspensionNuChoiceParameterIso R A I J K P Q T a).precomp r =
      dgKappaSuspensionNuChoiceParameterIso R A I J K P Q T (r ≫ a) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp _ _ _

end SerrePositivity.KST.NonConnective
