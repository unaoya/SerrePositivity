module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorPostOverPre
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorPostVertexIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：元の相対頂点比較から得た後合成の関手同型は、元の底上の前合成に対して自然。
方針：両側を同じ指定頂点比較の豊穣後合成の像へ戻し、全 Hom の自然性を使う。
規約：指定値を再選択しない。使われ方：三つの全選択族の指定関係を元の全空間へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B C D E Q : SSet.{u}}
  (p : C ⟶ B) (d : D ⟶ B) (q : E ⟶ B) (r : Q ⟶ B)
  [LeftFibration q] [LeftFibration r] (t : D ⟶ C) (ht : t ≫ p = d)
  (f g : E ⟶ Q) (hf : f ≫ r = q) (hg : g ≫ r = q)
  (e : VertexIso (relativeFunctorVertex r q f hf) (relativeFunctorVertex r q g hg))
local notation "a" => Over.homMk (U := Over.mk d) (V := Over.mk p) t ht
local notation "L" => relativeFunctorOverPre q a
local notation "M" => relativeFunctorOverPre r a
local notation "R₀" => relativeFunctorPostHom (Over.mk p) (Over.mk q) (Over.mk r)
local notation "R₁" => relativeFunctorPostHom (Over.mk d) (Over.mk q) (Over.mk r)
local notation "P₀" => relativeFunctorPostVertexIso p q r f g hf hg e
local notation "P₁" => relativeFunctorPostVertexIso d q r f g hf hg e

omit [LeftFibration q] [LeftFibration r] in
/-- 元の指定後合成比較の二通りの底上の制限は、元の同じ指定値を保持する。 -/
lemma relativeFunctorPostVertexIso_overPre_heq :
    HEq ((P₀).postcomp M) ((P₁).precomp L) := by
  let A₀ := relativeFunctorSpace q p
  let A₁ := relativeFunctorSpace r d
  have h₀ := vertexIso_map_heq_of_heq P₀ (VertexIso.map e R₀)
    (relativeFunctorPostHom_vertex (Over.mk p) (Over.mk q) (Over.mk r) (Over.homMk f hf)).symm
    (relativeFunctorPostHom_vertex (Over.mk p) (Over.mk q) (Over.mk r) (Over.homMk g hg)).symm
    (relativeFunctorPostVertexIso_heq_map p q r f g hf hg e) ((ihom A₀).map M)
  have h₁ := vertexIso_map_heq_of_heq P₁ (VertexIso.map e R₁)
    (relativeFunctorPostHom_vertex (Over.mk d) (Over.mk q) (Over.mk r) (Over.homMk f hf)).symm
    (relativeFunctorPostHom_vertex (Over.mk d) (Over.mk q) (Over.mk r) (Over.homMk g hg)).symm
    (relativeFunctorPostVertexIso_heq_map d q r f g hf hg e) ((pre L).app A₁)
  have hp : HEq ((P₀).postcomp M) (VertexIso.map P₀ ((ihom A₀).map M)) := by
    rw [functorIso_postcomp_eq_mapIso]
    rfl
  have hq : HEq ((P₁).precomp L) (VertexIso.map P₁ ((pre L).app A₁)) := by
    rw [functorIso_precomp_eq_mapIso]
    rfl
  exact (hp.trans (h₀.trans (heq_of_eq (vertexIso_map_comp e R₀ ((ihom A₀).map M))))).trans
    ((vertexIso_map_heq e (relativeFunctorPostHom_overPre a (Over.mk q) (Over.mk r))).trans
      (hq.trans (h₁.trans (heq_of_eq (vertexIso_map_comp e R₁ ((pre L).app A₁))))).symm)

end SerrePositivity.InfinityCategories.F2
