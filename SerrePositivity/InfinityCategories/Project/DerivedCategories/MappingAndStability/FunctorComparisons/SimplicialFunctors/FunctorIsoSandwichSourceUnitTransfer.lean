module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoSandwichUnitComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoSandwichCompositorNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoIdentityHorizontalSquare
/-!
概要：実模型の単位正方形と tensor 単位を一般 cell 合成子の始域単位三角式へ移す。
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
lemma functorIsoSandwichCompositor_source_unit_transfer {A X C Z : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory C] [Quasicategory Z]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A X) (t : C ⟶ Z)
    (F : X ⟶ X) (G : X ⟶ Z) (M : A ⟶ A) (N T : A ⟶ C)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (e.inv ≫ M ≫ e.hom)) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G (e.inv ≫ N ≫ t))
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (M ≫ N) T) (u : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (𝟙 X))
    (m : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso M (𝟙 A)) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso T N)
    (ha : a ≪≫ (m.postcomp e.hom).precomp e.inv = u ≪≫ e.invHomIso.symm)
    (hk : k ≪≫ r = m.postcomp N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor e.inv e.hom e.inv t e.coherentHomInvIso
        F G M N T a b k ≪≫ (r.postcomp t).precomp e.inv ≪≫ b.symm = u.postcomp G := by
  have ha' := congrArg Iso.hom ha
  have hk' := congrArg Iso.hom hk
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_hom_naturality
    (X := X) (A := A) (B := A) (Y := X) (C := C) (Z := Z)
    (F := F) (F' := 𝟙 X) (G := G) (G' := G)
    (M := M) (M' := 𝟙 A) (N := N) (N' := N) (T := T) (T' := N)
    e.inv e.hom e.inv t e.coherentHomInvIso a e.invHomIso.symm b b k (Iso.refl _)
    u.hom (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)))
    m.hom (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex N))) r.hom
    (by simpa only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed, Iso.symm_hom] using! ha')
    (by simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_identity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_identity,
      Category.comp_id, Category.id_comp])
    (by simpa only [Iso.trans_hom, Iso.refl_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_identity, Category.comp_id] using! hk')
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_coherent_left_unit_comparison e N t G b] at hn
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_identity, Category.comp_id] at hn
  have hh := congrArg (fun z ↦ z ≫ b.inv) hn
  apply Iso.ext
  simpa only [Iso.trans_hom, Iso.symm_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed, Category.assoc, Iso.hom_inv_id, Category.comp_id] using! hh
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
