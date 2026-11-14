module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomSquareTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomWhiskerMapTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FunctorHomPrecompAlgebra
/-!
概要：元の augmentation の自然性を、二射影と同じ指定入力切断の表示へ移す。
方針：同じ全関手射の端点輸送と二段前合成の整合性を保つ。
規約：指定比較と切断・計算上限を変更しない。使われ方：元の κ の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma functorIso_square_precomp_retract {W X Z Y : SSet.{w}}
    (s : W ⟶ X) (p : X ⟶ W) (g : X ⟶ Z) (f : W ⟶ Z)
    (hsp : s ≫ p = 𝟙 W) (hsg : s ≫ g = f)
    (u0 u1 : Z ⟶ Y) (v0 v1 : W ⟶ Y)
    (a0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ u0) (p ≫ v0))
    (a1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ u1) (p ≫ v1))
    (di : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom u0 u1) (df : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom v0 v1)
    (ha : a0.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp v0 v1 p df =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp u0 u1 g di ≫ a1.hom)
    (b0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ u0) v0) (b1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ u1) v1)
    (hb0 : HEq b0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp a0 s))
    (hb1 : HEq b1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp a1 s)) :
    b0.hom ≫ df = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp u0 u1 f di ≫ b1.hom := by
  have hs (u : Z ⟶ Y) : f ≫ u = s ≫ g ≫ u := by rw [← hsg, Category.assoc]
  have ht (v : W ⟶ Y) : v = s ≫ p ≫ v := by rw [← Category.assoc, hsp, Category.id_comp]
  have h0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq_of_endpoint_heq b0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp a0 s)
    (hs u0) (ht v0) hb0
  have h1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq_of_endpoint_heq b1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp a1 s)
    (hs u1) (ht v1) hb1
  have hd0 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_precomp v0 v1 p s df)
  have hd1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_heq_of_source_eq df hsp
  have hd2 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_id df)
  have hd := (hd0.trans (hd1.trans hd2)).symm
  have hi0 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_precomp u0 u1 g s di)
  have hi1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_heq_of_source_eq di hsg
  have hi := (hi0.trans hi1).symm
  have hp := congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (g ≫ u0) (p ≫ v1) =>
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (g ≫ u0) (p ≫ v1) s a) ha
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_comp] at hp
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_two_two_eq_of_heq _ _ _ _ _ _ _ _
    (hs u0) (ht v0) (hs u1) (ht v1) h0 hd hi h1 hp
end SerrePositivity.InfinityCategories.Project.DerivedCategories
