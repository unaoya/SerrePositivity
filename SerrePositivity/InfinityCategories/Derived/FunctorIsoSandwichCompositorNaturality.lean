module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoSandwichCompositor
/-!
概要：一般の両側比較から三段の合成比較の全射自然性を導く。
方針：元の比較値と任意全関手射の可換四角形を保持する。
規約：追加の選択や可逆性を要求しない。使われ方：一般 cell 合成子の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "po" => functorHomPostcomp
local notation "pr" => functorHomPrecomp
lemma functorIsoSandwichCompositor_hom_naturality {X A B Y C Z : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory Y]
    [Quasicategory C] [Quasicategory Z]
    (s : X ⟶ A) (h : B ⟶ Y) (i : Y ⟶ B) (t : C ⟶ Z)
    (e : FunctorIso (h ≫ i) (𝟙 B))
    {F F' : X ⟶ Y} {G G' : Y ⟶ Z}
    {M M' : A ⟶ B} {N N' : B ⟶ C} {T T' : A ⟶ C}
    (a : FunctorIso F (s ≫ M ≫ h)) (a' : FunctorIso F' (s ≫ M' ≫ h))
    (b : FunctorIso G (i ≫ N ≫ t)) (b' : FunctorIso G' (i ≫ N' ≫ t))
    (k : FunctorIso (M ≫ N) T) (k' : FunctorIso (M' ≫ N') T')
    (f : FunctorHom F F') (g : FunctorHom G G')
    (m : FunctorHom M M') (n : FunctorHom N N') (r : FunctorHom T T')
    (ha : a.hom ≫ pr (M ≫ h) (M' ≫ h) s (po M M' h m) = f ≫ a'.hom)
    (hb : b.hom ≫ pr (N ≫ t) (N' ≫ t) i (po N N' t n) = g ≫ b'.hom)
    (hk : k.hom ≫ r = (po M M' N m ≫ pr N N' M' n) ≫ k'.hom) :
    (functorIsoSandwichCompositor s h i t e F G M N T a b k).hom ≫
        pr (T ≫ t) (T' ≫ t) s (po T T' t r) =
      (po F F' G f ≫ pr G G' F' g) ≫
        (functorIsoSandwichCompositor s h i t e F' G' M' N' T' a' b' k').hom := by
  let u := pr (M ≫ h) (M' ≫ h) s (po M M' h m)
  let v := pr (N ≫ t) (N' ≫ t) i (po N N' t n)
  let j := po (s ≫ M ≫ h) (s ≫ M' ≫ h) (i ≫ N ≫ t) u ≫
    pr (i ≫ N ≫ t) (i ≫ N' ≫ t) (s ≫ M' ≫ h) v
  let l := pr ((M ≫ N) ≫ t) ((M' ≫ N') ≫ t) s
    (po (M ≫ N) (M' ≫ N') t (po M M' N m ≫ pr N N' M' n))
  have hn := functorIsoHorizontal_hom_naturality a a' b b' f u g v ha hb
  have hd : ((e.postcomp (N ≫ t)).precomp (s ≫ M)).hom ≫ l =
      j ≫ ((e.postcomp (N' ≫ t)).precomp (s ≫ M')).hom := by
    have q := functorIsoCancellation_hom_naturality h i e
      (pr M M' s m) (po N N' t n)
    have hp := functorHomPrecomp_precomp (N ≫ t) (N' ≫ t) M' s (po N N' t n)
    have hs := functorHomPrecomp_heq_of_source_eq
      (pr (N ≫ t) (N' ≫ t) i (po N N' t n)) (Category.assoc s M' h)
    have hs' := eq_of_heq hs
    simp only [functorHomPrecomp, functorHomPostcomp] at hp hs'
    simpa only [l, j, u, v, functorHomPrecomp, functorHomPostcomp,
      CategoryTheory.Functor.map_comp, functorHom_precomp_postcomp,
      functorHom_postcomp_postcomp, functorHom_precomp_precomp, hp, hs',
      Category.assoc] using! q
  have hc : ((k.postcomp t).precomp s).hom ≫
      pr (T ≫ t) (T' ≫ t) s (po T T' t r) =
      l ≫ ((k'.postcomp t).precomp s).hom := by
    have q := functorHomPostcomp_iso_square k k' (po M M' N m ≫ pr N N' M' n) r t hk
    have q' := congrArg
      (fun z => pr ((M ≫ N) ≫ t) (T' ≫ t) s z) q
    simpa only [l, functorHomPrecomp_comp, functorIso_precomp_hom_typed] using! q'
  simpa only [functorIsoSandwichCompositor, Iso.trans_hom, Category.assoc] using!
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
end SerrePositivity.InfinityCategories
