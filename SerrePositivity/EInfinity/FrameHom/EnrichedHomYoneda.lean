module

public import SerrePositivity.EInfinity.FrameHom.EnrichedHomRealization
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentableHomInfinity

/-!
概要：E2 の元の豊穣 Hom 実現へ正本の全 Yoneda 比較を代入する。
方針：元の豊穣関手の全作用を厳密に同定して原本の関手同型を使う。
規約：原本の複製や点ごとの比較による全図式同型の推測はしない。
使われ方：同じ hammock 終端から正本 Hom∞ への無条件の全比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
variable {D : Type u} [Category.{u} D] [SimplicialCategory D]
  [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：先行構成した豊穣 Hom 関手は原本の関手と一致する。
方針：同じ対象と全合成作用を照合する。
規約：原本を再定義しない。使われ方：全 Yoneda 比較の直接代入。 -/
lemma enrichedHomFunctor_eq_representableHomFunctor (x : D) :
    enrichedHomFunctor x = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomFunctor x := by
  apply EnrichedFunctor.ext SSet (fun _ => rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]

/-- 概要：元の coherent 全実現は正本の全実現と一致する。
方針：同じ豊穣関手の等式を全単体へ適用する。
規約：全図式の等式。使われ方：同じ Yoneda 全同型の始域の照合。 -/
lemma enrichedHomCoherent_eq_representableHomCoherent (x : D) :
    enrichedHomCoherent x = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomCoherent x := by
  simp only [enrichedHomCoherent, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomCoherent, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallKanRealization,
    enrichedHomFunctor_eq_representableHomFunctor]

/-- 概要：元の豊穣 Hom 実現から正本の共変 Hom への全同型。
方針：全実現を厳密に照合し、原本の全 Yoneda 同型を使う。
規約：点ごとの値同値に還元しない。使われ方：hammock への直接代入。 -/
def enrichedHomYonedaIso (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (enrichedHomCoherent x) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) := by
  rw [enrichedHomCoherent_eq_representableHomCoherent]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomCoherentIso x

end SerrePositivity.EInfinity.FrameHom
