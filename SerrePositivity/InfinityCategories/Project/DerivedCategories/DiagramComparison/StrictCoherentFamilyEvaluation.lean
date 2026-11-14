module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.OrderedSimplexPullback
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
概要：全 HA 成分に可換する厳密な coherent 族を、全 nerve と添字の同時評価にする。
方針：有限射列の対角の単体を使い、面・退化の二重の引き戻しを照合する。
規約：対象ごとの余錐だけで全族が自然とは扱わない。元の成分の整合性を全て使用する。
使われ方：3b-3 R6、指定余錐の全パラメーター族。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
open CategoryTheory SSet MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
namespace OrderedSimplexFamily
variable {A : Type u} [CommRing A] {E : Type v} [DGCategory A E] {n : ℕ}

/-- 同じ頂点族と全厳密写像を持つ有限 HA 族は同じ。 -/
lemma ext {d e : OrderedSimplexFamily A E n}
    (ho : ∀ a, d.obj a = e.obj a)
    (hm : ∀ a b hab, HEq (d.map a b hab) (e.map a b hab)) : d = e := by
  cases d with
  | mk f m hi hc =>
    cases e with
    | mk g k hj hd =>
      have hfg : f = g := funext ho
      cases hfg
      have hmk : m = k := by
        funext a b hab
        exact eq_of_heq (hm a b hab)
      cases hmk
      rfl

end OrderedSimplexFamily
namespace StrictCoherentFamily
variable {A : Type u} [CommRing A] {E : Type v} [DGCategory A E]
  {I : SSet.{u}} {C : Type w} [Category.{w'} C]

/-- 元の全 HA 族から有限射列への評価は、二つの同時引き戻しに自然である。 -/
lemma orderedSimplexFamily_pullback (F : StrictCoherentFamily A E I C) {m n : ℕ}
    (d : Fin (n + 1) ⥤ C) (s : I _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1)) :
    F.orderedSimplexFamily
        ((nerve C).map (SimplexCategory.mkHom α).op d)
        (I.map (SimplexCategory.mkHom α).op s) =
      (F.orderedSimplexFamily d s).pullback α := by
  apply OrderedSimplexFamily.ext
  · intro a
    exact coherentDiagramSimplex_map (F.obj (d.obj (α a))) α s
  · intro a b hab
    exact F.map_pullback (d.map (homOfLE (α.monotone hab))) α s

/-- 定値のパラメーター射列では、全 HA 単体が元の同じ単体へ戻る。 -/
lemma orderedSimplexFamily_const (F : StrictCoherentFamily A E I C) (c : C)
    {n : ℕ} (s : I _⦋n⦌) :
    (F.orderedSimplexFamily ((Functor.const (Fin (n + 1))).obj c) s).diagonal =
      coherentDiagramSimplex (F.obj c) s := by
  apply Simplex.ext
  apply SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext T a b k hT ha hb hk
    change compose A ((F.map (𝟙 c) s).app b).val
        ((coherentDiagramSimplex (F.obj c) s).hom T a b k hT ha hb hk) (add_zero k) = _
    rw [F.map_id]
    exact unit_compose A _

end StrictCoherentFamily
namespace StrictCoherentFamily
variable {A : Type u} [CommRing A] {E : Type (u + 1)} [DGCategory A E]
  {I : SSet.{u}} {C : Type (u + 1)} [Category.{u} C]

/-- 元の全 HA 成分と射列を同時に評価する全単体的写像。 -/
def evaluation (F : StrictCoherentFamily A E I C) :
    nerve C ⊗ (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ dgNerve A E where
  app n := ↾fun s => (F.orderedSimplexFamily s.1 s.2.down).diagonal
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    rintro ⟨d, s⟩
    change (F.orderedSimplexFamily ((nerve C).map α d) (I.map α s.down)).diagonal =
      (F.orderedSimplexFamily d s.down).diagonal.pullback α.unop.toOrderHom
    exact (congrArg OrderedSimplexFamily.diagonal
      (F.orderedSimplexFamily_pullback d s.down α.unop.toOrderHom)).trans
        ((F.orderedSimplexFamily d s.down).diagonal_pullback α.unop.toOrderHom)

end StrictCoherentFamily
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
