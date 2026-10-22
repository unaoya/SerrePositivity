module

public import SerrePositivity.InfinityCategories.Core.CodiscreteNerve
public import SerrePositivity.InfinityCategories.Core.Join

/-!
概要：元の codiscrete ラベル写像を、指定した新しい頂点ラベルを持つ錐へ延長する。
方針：join の零単体の左右を分け、既存の codiscrete nerve の頂点による構成を適用する。
規約：元の底上の写像と右頂点の写像を厳密に保つ。
使われ方：κ-small な部分複体の錐を未使用ラベルで単射に埋め込む構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {K : SSet.{u}} {T : Type u}

/-- 元の頂点ラベルと指定した右頂点ラベルをまとめた同じ錐の頂点関数。 -/
def coneVertexLabels (f : K _⦋0⦌ → T) (a : T) : (join K (Δ[0] : SSet.{u})) _⦋0⦌ → T := by
  intro s
  exact if h : s.1.val = 0 then a else
    f (cast (congrArg (Join.augObj K) (by
      have hi : s.1.val < 2 := s.1.isLt
      omega : s.1.val = 1)) s.2.1)

/-- 元のラベル写像を、指定した頂点ラベルを持つ同じ錐へ延長する。 -/
def codiscreteConeLabelMap (f : K ⟶ nerve (Codiscrete T)) (a : T) :
    join K (Δ[0] : SSet.{u}) ⟶ nerve (Codiscrete T) :=
  codiscreteNerveMap (coneVertexLabels (fun x => (nerveEquiv (f.app _ x)).as) a)

/-- 同じ錐のラベル写像は、元の底のラベル写像に厳密に制限する。 -/
lemma codiscreteConeLabelMap_inl (f : K ⟶ nerve (Codiscrete T)) (a : T) :
    joinInl K Δ[0] ≫ codiscreteConeLabelMap f a = f := by
  apply codiscreteNerve_hom_ext
  intro x
  change (nerveEquiv ((codiscreteNerveMap _).app _ ((joinInl K Δ[0]).app _ x))).as = _
  rw [codiscreteNerveMap_vertex]
  rfl

/-- 同じ錐の右頂点の像は指定した同じラベル。 -/
lemma codiscreteConeLabelMap_inr (f : K ⟶ nerve (Codiscrete T)) (a : T) :
    joinInr K Δ[0] ≫ codiscreteConeLabelMap f a =
      SSet.const (nerveVertex (Codiscrete.mk a)) := by
  apply codiscreteNerve_hom_ext
  intro x
  change (nerveEquiv ((codiscreteNerveMap _).app _ ((joinInr K Δ[0]).app _ x))).as = a
  rw [codiscreteNerveMap_vertex]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
