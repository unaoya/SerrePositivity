module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoInverseSourceComparison
/-!
概要：前向きの二つの単位正方形を指定逆に沿う cell 単位正方形へ移す。
方針：同じ共通 graph 比較の相殺と h Fun の実交換則を使う。
規約：同値の三角式は仮定しない。使われ方：元の diagonal cell 比較の単位。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIso_inverse_cell_unit {A X : SSet.{u}} [Quasicategory X]
    (h : A ⟶ X) (s : X ⟶ A) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (s ≫ h) (𝟙 X))
    (F : X ⟶ X) (G : A ⟶ A) (T : A ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (h ≫ F) T) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ≫ h) T) (v : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso T h)
    (uF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (𝟙 X)) (uG : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G (𝟙 A))
    (ha : a ≪≫ v = uF.precomp h) (hb : b ≪≫ v = uG.postcomp h) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp d.symm F ≪≫ a.precomp s ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp b.symm s) ≪≫
      (uG.postcomp h).precomp s = uF ≪≫ d.symm := by
  have hc : a ≪≫ b.symm ≪≫ uG.postcomp h = uF.precomp h := by
    rw [← hb]
    simpa only [Iso.symm_self_id_assoc] using ha
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp d.symm F ≪≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (f := h ≫ F) (g := h)
          (a ≪≫ b.symm ≪≫ uG.postcomp h) s := by
      simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, Iso.trans_assoc]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp d.symm F ≪≫ (uF.precomp h).precomp s := by rw [hc]
    _ = _ := by
      have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_whisker_exchange d.symm uF
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_id,
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_id] using! hx
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
