module
public import SerrePositivity.KST.Fibration.RelativeDiagramMap

/-! # 相対図式の core 包含と商の選択独立性

可逆な自然変換は成分ごとに W に属する。同じ包含に対する二つの Verdier 商は
全単体に同じ部分複体を定める。いずれも実一単体から全高次単体へ条件を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 図式の core は成分ごとの弱同値の部分複体に含まれる。 -/
def relativeDiagramCoreInclusion {B C X : SSet.{u}} {J : Type v}
    (q : B ⟶ C) (ev : J → (X ⟶ B)) :
    (quasicategoryCore X : SSet.{u}) ⟶ (relativeDiagram q ev : SSet.{u}) :=
  Subcomplex.lift (quasicategoryCore X).ι (by
    rintro n _ ⟨s, rfl⟩ j
    exact ((quasicategoryCoreMap (ev j ≫ q)).app n s).property)

/-- core 包含は周囲への実包含を回収する。 -/
lemma relativeDiagramCoreInclusion_ι {B C X : SSet.{u}} {J : Type v}
    (q : B ⟶ C) (ev : J → (X ⟶ B)) :
    relativeDiagramCoreInclusion q ev ≫ (relativeDiagram q ev).ι =
      (quasicategoryCore X).ι := rfl

/-- core からの包含は、評価と可換な再添字射に関して自然。 -/
lemma relativeDiagramCoreInclusion_naturality {B C X Y : SSet.{u}}
    {J K : Type v} (q : B ⟶ C) (evX : J → (X ⟶ B)) (evY : K → (Y ⟶ B))
    (f : X ⟶ Y) (r : K → J) (hf : ∀ k, f ≫ evY k = evX (r k)) :
    relativeDiagramCoreInclusion q evX ≫ relativeDiagramMap q evX evY f r hf =
      quasicategoryCoreMap f ≫ relativeDiagramCoreInclusion q evY := by
  apply (cancel_mono (relativeDiagram q evY).ι).1
  rw [Category.assoc, relativeDiagramMap_ι, ← Category.assoc,
    relativeDiagramCoreInclusion_ι, Category.assoc, relativeDiagramCoreInclusion_ι,
    quasicategoryCoreMap_ι]

/-- 同じ包含の二つの実 Verdier 商は全高次単体を含めて同じ相対図式を与える。 -/
lemma relativeDiagram_eq_of_verdier
    {A B C D : StableCategory.{u}} {i : ExactMap A B}
    {q : ExactMap B C} {p : ExactMap B D}
    (hq : IsVerdierSequence i q) (hp : IsVerdierSequence i p)
    {X : SSet.{u}} {J : Type v} (ev : J → (X ⟶ B.obj)) :
    relativeDiagram q.hom ev = relativeDiagram p.hom ev := by
  ext n s
  exact (relativeDiagram_mem_iff hq ev s).trans (relativeDiagram_mem_iff hp ev s).symm

end SerrePositivity.KST.Fibration
