module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange
/-!
概要：二つの対角 kernel を使う三角式と左単位の coherence を、同じ全関手同型で扱う。
方針：元の dg 三角・全関手同型の実交換則・同じ指定単位を保つ。
規約：原 Hom の平坦性を追加しない。使われ方：元の導来 kernel の左単位三角式。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
/-- 恒等への同じ指定同型を持つ関手への後合成は、全関手同型の等式を反映する。 -/
lemma functorIso_postcomp_reflect_of_unit {X Y : SSet.{u}} [Quasicategory Y]
    (T : Y ⟶ Y) (v : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso T (𝟙 Y)) {F G : X ⟶ Y}
    (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) (h : a.postcomp T = b.postcomp T) : a = b := by
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_whisker_exchange a v
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_whisker_exchange b v
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_id] at ha hb
  have hc := congrArg (fun e => e ≪≫ v.precomp G) h
  have he := ha.symm.trans (hc.trans hb)
  apply Iso.ext
  exact (cancel_epi (v.precomp F).hom).mp (congrArg Iso.hom he)
/-- 元の五角式・右単位三角式・自然性四角形と三角式は、左単位三角式を与える。 -/
lemma leftUnitComparison_from_pentagon {X Y : SSet.{u}} [Quasicategory Y]
    (F : X ⟶ Y) (T : Y ⟶ Y) (G : X ⟶ Y) (U : Y ⟶ Y) (V W : X ⟶ Y)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ T) G) (j : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G F) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso U T)
    (k₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (T ≫ T) U) (k₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ≫ T) V)
    (k₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ U) W) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso W V)
    (l : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso V G) (q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso W G) (v : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso T (𝟙 Y))
    (htriangle : a ≪≫ l = q) (hfirst : k₂ ≪≫ l = j.postcomp T ≪≫ c)
    (hsecond : k₃ ≪≫ q = r.precomp F ≪≫ c) (hright : k₁ ≪≫ r = v.postcomp T)
    (hpent : c.postcomp T ≪≫ k₂ = k₁.precomp F ≪≫ k₃ ≪≫ a) : c ≪≫ j = v.precomp F := by
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (c ≪≫ j) T ≪≫ c = (v.postcomp T).precomp F ≪≫ c := by
    calc
      _ = c.postcomp T ≪≫ (j.postcomp T ≪≫ c) := by
        rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, Iso.trans_assoc]
      _ = c.postcomp T ≪≫ (k₂ ≪≫ l) := by rw [← hfirst]
      _ = (c.postcomp T ≪≫ k₂) ≪≫ l := (Iso.trans_assoc _ _ _).symm
      _ = (k₁.precomp F ≪≫ k₃ ≪≫ a) ≪≫ l := by rw [hpent]
      _ = k₁.precomp F ≪≫ k₃ ≪≫ q := by
        simp only [Iso.trans_assoc]
        rw [htriangle]
      _ = k₁.precomp F ≪≫ (r.precomp F ≪≫ c) := by rw [hsecond]
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (k₁ ≪≫ r) F ≪≫ c := by
        rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, Iso.trans_assoc]
      _ = _ := by rw [hright]
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (c ≪≫ j) T = (v.postcomp T).precomp F := by
    apply Iso.ext
    exact (cancel_mono c.hom).mp (congrArg Iso.hom hh)
  apply functorIso_postcomp_reflect_of_unit T v (c ≪≫ j) (v.precomp F)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp] using! he
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
