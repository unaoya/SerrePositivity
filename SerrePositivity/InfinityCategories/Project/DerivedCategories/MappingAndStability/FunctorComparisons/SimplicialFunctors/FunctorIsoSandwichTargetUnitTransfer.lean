module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoSandwichTargetUnitComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoSandwichCompositorNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoIdentityHorizontalSquare
/-!
概要：実模型の単位正方形と tensor 単位を一般 cell 合成子の終域単位三角式へ移す。
方針：同じ全射自然性に指定単位を入れ、coherent な恒等模型の単位式を使う。
規約：tensor 単位は別途与えられた実比較。使われ方：元の kernel の単位 coherence。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIsoSandwichCompositor_target_unit_transfer {X A B Y : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory Y]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence B Y) (s : X ⟶ A)
    (F : X ⟶ Y) (G : Y ⟶ Y) (M : A ⟶ B) (N : B ⟶ B) (T : A ⟶ B)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (s ≫ M ≫ e.hom)) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G (e.inv ≫ N ≫ e.hom))
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (M ≫ N) T) (u : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G (𝟙 Y))
    (n : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso N (𝟙 B)) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso T M)
    (hb : b ≪≫ (n.postcomp e.hom).precomp e.inv = u ≪≫ e.invHomIso.symm)
    (hk : k ≪≫ r = n.precomp M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor s e.hom e.inv e.hom e.coherentHomInvIso
        F G M N T a b k ≪≫ (r.postcomp e.hom).precomp s ≪≫ a.symm = u.precomp F := by
  have hb' := congrArg Iso.hom hb
  have hk' := congrArg Iso.hom hk
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_hom_naturality
    (X := X) (A := A) (B := B) (Y := Y) (C := B) (Z := Y)
    (F := F) (F' := F) (G := G) (G' := 𝟙 Y)
    (M := M) (M' := M) (N := N) (N' := 𝟙 B) (T := T) (T' := M)
    s e.hom e.inv e.hom e.coherentHomInvIso a a b e.invHomIso.symm k (Iso.refl _)
    (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))) u.hom
    (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex M))) n.hom r.hom
    (by simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_identity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_identity,
      Category.comp_id, Category.id_comp])
    (by simpa only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed, Iso.symm_hom] using! hb')
    (by simpa only [Iso.trans_hom, Iso.refl_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_identity, Category.id_comp, Category.comp_id] using! hk')
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_coherent_right_unit_comparison e s M F a] at hn
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_identity, Category.id_comp] at hn
  have hh := congrArg (fun z ↦ z ≫ a.inv) hn
  apply Iso.ext
  simpa only [Iso.trans_hom, Iso.symm_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed, Category.assoc, Iso.hom_inv_id, Category.comp_id] using! hh
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
