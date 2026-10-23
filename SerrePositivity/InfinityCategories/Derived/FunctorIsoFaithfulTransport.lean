module
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerAlgebra
/-!
概要：指定全関手同型の合成輸送と、完全充満な後合成による等式反映。
方針：三つの端点等式を明示して消去し、全関手圏の忠実性を使う。
規約：対象成分の一致だけから同型の一致を結論しない。使われ方：分解比較の合成則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
/-- 三端点の等式と同じ指定値の一致は、二つの全関手同型の合成にも保たれる。 -/
lemma functorIso_trans_heq {X Y : SSet.{u}} {f g h f' g' h' : X ⟶ Y}
    (e : FunctorIso f g) (d : FunctorIso g h)
    (e' : FunctorIso f' g') (d' : FunctorIso g' h')
    (hf : f = f') (hg : g = g') (hh : h = h')
    (he : HEq e e') (hd : HEq d d') : HEq (e ≪≫ d) (e' ≪≫ d') := by
  subst f' g' h'
  cases eq_of_heq he
  cases eq_of_heq hd
  rfl
/-- 完全充満な実写像への後合成は、全関手同型そのものの等式を反映する。 -/
lemma functorIso_postcomp_injective_of_isFullyFaithful {X Y K : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {q : X ⟶ Y} (hq : IsFullyFaithful q)
    {f g : K ⟶ X} : Function.Injective (fun e : FunctorIso f g => e.postcomp q) := by
  intro e d h
  apply Iso.ext
  apply (hq.postcompose K).toHoFullyFaithful.map_injective
  have hh := congrArg Iso.hom h
  simpa only [F2.functorIso_postcomp_eq_mapIso, Functor.mapIso_hom] using! hh
end SerrePositivity.InfinityCategories
