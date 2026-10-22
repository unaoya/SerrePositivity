module

public import SerrePositivity.InfinityCategories.F2.CoherentPrefixPathCoordinates
public import SerrePositivity.InfinityCategories.F2.CoherentPrefixPathComposition

/-!
概要：prefix 変形を simplicial thickening 間の実際の豊穣関手にする。
方針：path の包含の関手の nerve と、恒等・合成の厳密な式を使う。
規約：最大化から元の図式への向き、固定始点の全座標を保持する。
使われ方：零面の全族比較の指定精密化の実代表。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2

/-- prefix 変形は同じ二端点間の path の圏の関手。 -/
def coherentPrefixPathDeformationFunctor {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) (i j : J) : Path i j ⥤ Path (A i) (A j) where
  obj P := coherentPrefixPathDeformation A t P
  map f := ⟨⟨⟨coherentPrefixPathDeformation_mono A t f.1.1.1⟩⟩⟩

/-- prefix 変形の豊穣関手は元の対象写像と全ての精密化を保持する。 -/
def coherentPrefixPathDeformationEnriched {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) :
    EnrichedFunctor SSet.{u} (SimplicialThickening J) (SimplicialThickening K) where
  obj i := ⟨A i.as⟩
  map i j := nerveMap (coherentPrefixPathDeformationFunctor A t i.as j.as)
  map_id i := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    apply CategoryTheory.Functor.ext (fun _ ↦ coherentPrefixPathDeformation_id A t i.as)
  map_comp i j k := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    apply CategoryTheory.Functor.ext
      (fun z ↦ coherentPrefixPathDeformation_comp A t (P.obj z) (Q.obj z))

/-- prefix 変形の豊穣関手は元の添字変換と可換。 -/
lemma coherentPrefixPathDeformationEnriched_reindex {I J K : Type u}
    [LinearOrder I] [LinearOrder J] [LinearOrder K]
    (g : I →o J) (A : J →o K) (t : J →o Fin 2) :
    (SimplicialThickening.functor g).comp SSet (coherentPrefixPathDeformationEnriched A t) =
      coherentPrefixPathDeformationEnriched (A.comp g) (t.comp g) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext
    (fun z ↦ (coherentPrefixPathDeformation_reindex g A t (P.obj z)).symm)

end SerrePositivity.InfinityCategories.F2
