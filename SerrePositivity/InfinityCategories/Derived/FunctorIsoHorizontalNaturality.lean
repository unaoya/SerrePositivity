module
public import SerrePositivity.InfinityCategories.Derived.ActionComparisonHomNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPostcompIdentity
/-!
概要：二つの全関手比較の水平合成は任意全関手射に自然である。
方針：指定比較四角形の水平合成則を恒等の辺へ適用する。
規約：射の可逆性を要求しない。使われ方：一般 cell 合成比較の自然性。
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
lemma functorIsoHorizontal_hom_naturality {X Y Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z]
    {F F' G G' : X ⟶ Y} {H H' K K' : Y ⟶ Z}
    (a : FunctorIso F G) (a' : FunctorIso F' G')
    (b : FunctorIso H K) (b' : FunctorIso H' K')
    (e : FunctorHom F F') (e' : FunctorHom G G')
    (d : FunctorHom H H') (d' : FunctorHom K K')
    (ha : a.hom ≫ e' = e ≫ a'.hom) (hb : b.hom ≫ d' = d ≫ b'.hom) :
    (a.postcomp H ≪≫ b.precomp G).hom ≫
        (po G G' K e' ≫ pr K K' G' d') =
      (po F F' H e ≫ pr H H' F' d) ≫ (a'.postcomp H' ≪≫ b'.precomp G').hom := by
  have h := comparisonCompositionIso_hom_naturality (𝟙 X) (𝟙 Y) (𝟙 Z)
    F F' H H' G G' K K' a a' b b' e e' d d'
    (by simpa only [functorHom_postcomp_id, functorHomPrecomp, functorHom_precomp_id] using! ha)
    (by simpa only [functorHom_postcomp_id, functorHomPrecomp, functorHom_precomp_id] using! hb)
  simpa only [comparisonCompositionIso, functorHom_postcomp_id, functorHomPrecomp,
    functorHom_precomp_id] using! h
end
end SerrePositivity.InfinityCategories
