module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorPostIsoOverPre
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentPre

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
open scoped Simplicial
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

/-- 底上の制限後の指定成分は、元の指定成分を同じ制限で写した値そのもの。 -/
lemma relativeFunctorPostVertexIso_overPre_app_heq
    (x : (relativeFunctorSpace q p) _⦋0⦌) :
    HEq (VertexIso.map ((P₀).app x) M) ((P₁).app ((L).app _ x)) := by
  have h := functorIso_app_heq_of_heq ((P₀).postcomp M) ((P₁).precomp L)
    (relativeFunctorPost_overPre p d q r t ht f hf)
    (relativeFunctorPost_overPre p d q r t ht g hg)
    (relativeFunctorPostVertexIso_overPre_heq p d q r t ht f g hf hg e) x
  exact (functorIso_app_postcomp_heq P₀ M x).symm.trans
    (h.trans (functorIso_app_precomp_heq P₁ L x))

end SerrePositivity.InfinityCategories.F2
