module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPostcompIdentity
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPrecompAlgebra
/-!
概要：中間同値の消去は両側の任意全関手射に自然である。
方針：同じ消去同型と前後合成の交換則を二度使う。
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
lemma functorIsoCancellation_hom_naturality {U V W T : SSet.{u}}
    [Quasicategory V] [Quasicategory W] [Quasicategory T]
    (h : V ⟶ W) (i : W ⟶ V) (e : FunctorIso (h ≫ i) (𝟙 V))
    {A A' : U ⟶ V} {B B' : V ⟶ T}
    (a : FunctorHom A A') (b : FunctorHom B B') :
    ((e.postcomp B).precomp A).hom ≫
        (po A A' B a ≫ pr B B' A' b) =
      (po (A ≫ h) (A' ≫ h) (i ≫ B) (po A A' h a) ≫
        pr (i ≫ B) (i ≫ B') (A' ≫ h) (pr B B' i b)) ≫
        ((e.postcomp B').precomp A').hom := by
  have ha := functorHom_whisker_exchange_typed a (e.postcomp B).hom
  have hid : pr B B' (𝟙 V) b = b := functorHom_precomp_id b
  have hb := functorHom_whisker_exchange_typed e.hom b
  have hb' := congrArg (fun z => pr ((h ≫ i) ≫ B) B' A' z) hb
  have hbn : ((e.postcomp B).precomp A').hom ≫ pr B B' A' b =
      pr B B' (A' ≫ h ≫ i) b ≫ ((e.postcomp B').precomp A').hom := by
    simpa only [functorHomPrecomp_comp, functorIso_precomp_hom_typed,
      functorIso_postcomp_hom_typed, functorHomPrecomp_precomp,
      hid] using! hb'
  calc
    _ = (po A A' ((h ≫ i) ≫ B) a ≫
        ((e.postcomp B).precomp A').hom) ≫ pr B B' A' b := by
      simpa only [functorIso_precomp_hom_typed, Category.id_comp, Category.assoc] using!
        congrArg (fun z => z ≫ pr B B' A' b) ha.symm
    _ = po A A' ((h ≫ i) ≫ B) a ≫
        (pr B B' (A' ≫ h ≫ i) b ≫ ((e.postcomp B').precomp A').hom) := by
      simpa only [Category.assoc] using!
        congrArg (fun z => po A A' ((h ≫ i) ≫ B) a ≫ z) hbn
    _ = _ := by
      simp only [functorHomPostcomp_postcomp, functorHomPrecomp_precomp]
      exact (Category.assoc _ _ _).symm
end
end SerrePositivity.InfinityCategories
