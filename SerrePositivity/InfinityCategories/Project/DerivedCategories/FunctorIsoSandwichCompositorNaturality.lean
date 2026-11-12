module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoSandwichCompositor
/-!
概要：一般の両側比較から三段の合成比較の全射自然性を導く。
方針：元の比較値と任意全関手射の可換四角形を保持する。
規約：追加の選択や可逆性を要求しない。使われ方：一般 cell 合成子の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "po" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
local notation "pr" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
lemma functorIsoSandwichCompositor_hom_naturality {X A B Y C Z : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory Y]
    [Quasicategory C] [Quasicategory Z]
    (s : X ⟶ A) (h : B ⟶ Y) (i : Y ⟶ B) (t : C ⟶ Z)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (h ≫ i) (𝟙 B))
    {F F' : X ⟶ Y} {G G' : Y ⟶ Z}
    {M M' : A ⟶ B} {N N' : B ⟶ C} {T T' : A ⟶ C}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (s ≫ M ≫ h)) (a' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F' (s ≫ M' ≫ h))
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G (i ≫ N ≫ t)) (b' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G' (i ≫ N' ≫ t))
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (M ≫ N) T) (k' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (M' ≫ N') T')
    (f : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F F') (g : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G G')
    (m : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom M M') (n : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom N N') (r : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom T T')
    (ha : a.hom ≫ pr (M ≫ h) (M' ≫ h) s (po M M' h m) = f ≫ a'.hom)
    (hb : b.hom ≫ pr (N ≫ t) (N' ≫ t) i (po N N' t n) = g ≫ b'.hom)
    (hk : k.hom ≫ r = (po M M' N m ≫ pr N N' M' n) ≫ k'.hom) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor s h i t e F G M N T a b k).hom ≫
        pr (T ≫ t) (T' ≫ t) s (po T T' t r) =
      (po F F' G f ≫ pr G G' F' g) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor s h i t e F' G' M' N' T' a' b' k').hom := by
  let u := pr (M ≫ h) (M' ≫ h) s (po M M' h m)
  let v := pr (N ≫ t) (N' ≫ t) i (po N N' t n)
  let j := po (s ≫ M ≫ h) (s ≫ M' ≫ h) (i ≫ N ≫ t) u ≫
    pr (i ≫ N ≫ t) (i ≫ N' ≫ t) (s ≫ M' ≫ h) v
  let l := pr ((M ≫ N) ≫ t) ((M' ≫ N') ≫ t) s
    (po (M ≫ N) (M' ≫ N') t (po M M' N m ≫ pr N N' M' n))
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoHorizontal_hom_naturality a a' b b' f u g v ha hb
  have hd : ((e.postcomp (N ≫ t)).precomp (s ≫ M)).hom ≫ l =
      j ≫ ((e.postcomp (N' ≫ t)).precomp (s ≫ M')).hom := by
    have q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoCancellation_hom_naturality h i e
      (pr M M' s m) (po N N' t n)
    have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_precomp (N ≫ t) (N' ≫ t) M' s (po N N' t n)
    have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_heq_of_source_eq
      (pr (N ≫ t) (N' ≫ t) i (po N N' t n)) (Category.assoc s M' h)
    have hs' := eq_of_heq hs
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp] at hp hs'
    simpa only [l, j, u, v, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp,
      CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_postcomp,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_postcomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_precomp, hp, hs',
      Category.assoc] using! q
  have hc : ((k.postcomp t).precomp s).hom ≫
      pr (T ≫ t) (T' ≫ t) s (po T T' t r) =
      l ≫ ((k'.postcomp t).precomp s).hom := by
    have q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_iso_square k k' (po M M' N m ≫ pr N N' M' n) r t hk
    have q' := congrArg
      (fun z => pr ((M ≫ N) ≫ t) (T' ≫ t) s z) q
    simpa only [l, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed] using! q'
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor, Iso.trans_hom, Category.assoc] using!
    calc
      ((a.postcomp G ≪≫ b.precomp (s ≫ M ≫ h)).hom ≫
        ((e.postcomp (N ≫ t)).precomp (s ≫ M)).hom ≫
        ((k.postcomp t).precomp s).hom) ≫
          pr (T ≫ t) (T' ≫ t) s (po T T' t r) =
        (po F F' G f ≫ pr G G' F' g) ≫
          (a'.postcomp G' ≪≫ b'.precomp (s ≫ M' ≫ h)).hom ≫
          ((e.postcomp (N' ≫ t)).precomp (s ≫ M')).hom ≫
          ((k'.postcomp t).precomp s).hom := by
            calc
              _ = (a.postcomp G ≪≫ b.precomp (s ≫ M ≫ h)).hom ≫
                  ((e.postcomp (N ≫ t)).precomp (s ≫ M)).hom ≫
                  (l ≫ ((k'.postcomp t).precomp s).hom) := by
                    simpa only [Category.assoc] using!
                      congrArg (fun z => (a.postcomp G ≪≫ b.precomp (s ≫ M ≫ h)).hom ≫
                        ((e.postcomp (N ≫ t)).precomp (s ≫ M)).hom ≫ z) hc
              _ = (a.postcomp G ≪≫ b.precomp (s ≫ M ≫ h)).hom ≫
                  (j ≫ ((e.postcomp (N' ≫ t)).precomp (s ≫ M')).hom) ≫
                  ((k'.postcomp t).precomp s).hom := by
                    simpa only [Category.assoc] using!
                      congrArg (fun z => (a.postcomp G ≪≫ b.precomp (s ≫ M ≫ h)).hom ≫ z ≫
                        ((k'.postcomp t).precomp s).hom) hd
              _ = _ := by
                simpa only [j, u, v, Category.assoc] using!
                  congrArg (fun z => z ≫
                    ((e.postcomp (N' ≫ t)).precomp (s ≫ M')).hom ≫
                    ((k'.postcomp t).precomp s).hom) hn
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
