module
public import SerrePositivity.DifferentialGraded.Category.ObjectImage
public import SerrePositivity.InfinityCategories.Derived.DGFunctorFullyFaithful
public import SerrePositivity.InfinityCategories.Derived.DGFunctorTrivialFibration

/-! # dg 関手のラベル付き充満像への nerve の比較

概要：全射 Hom 準同型な dg 関手は同一宇宙の充満像へ ∞ 圏同値を与える。
方針：充満像への対象写像は常に全射なので、相対境界充填の一般定理を使う。
規約：元の標的 dg 圏の宇宙は任意。使われ方：β3 の dg Yoneda の代表部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
variable [DGCategory A D] [DGCategory A E]

/-- ラベル付き充満像への関手の Hom 複体は元の関手の Hom 複体。 -/
lemma dgFunctorToObjectImage_homQuasiIso (F : DGFunctor A D E) (hq : HomQuasiIso F) :
    HomQuasiIso (dgFunctorToObjectImage F) := hq

/-- 全射 Hom 準同型なら充満像への nerve は自明 Kan fibration。 -/
lemma dgFunctorToObjectImageNerve_trivialKanFibration (F : DGFunctor A D E)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i))
    (hq : HomQuasiIso F) : TrivialKanFibration (dgNerve.map (dgFunctorToObjectImage F)) :=
  dgNerve_map_trivialKanFibration_of_surjective_quasiIso _
    (dgFunctorToObjectImage_obj_surjective F) hs (dgFunctorToObjectImage_homQuasiIso F hq)

/-- 宇宙の異なる標的の充満像との明示的な ∞ 圏同値。 -/
def dgObjectImageNerveEquivalence (F : DGFunctor A D E)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i))
    (hq : HomQuasiIso F) : QCatEquivalence (dgNerve A D) (dgNerve A (DGObjectImage F.obj)) := by
  let := dgFunctorToObjectImageNerve_trivialKanFibration F hs hq
  exact qCatEquivalenceOfTrivialKanFibration (dgNerve.map (dgFunctorToObjectImage F))

/-- 充満像との同値の順方向は元の dg 関手の Hom 写像を持つ実際の nerve。 -/
lemma dgObjectImageNerveEquivalence_hom (F : DGFunctor A D E)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i)) (hq : HomQuasiIso F) :
    (dgObjectImageNerveEquivalence F hs hq).hom = dgNerve.map (dgFunctorToObjectImage F) := rfl

/-- Hom 複体同型からの充満像との明示的な ∞ 圏同値。 -/
def dgObjectImageNerveEquivalenceOfHomIso (F : DGFunctor A D E)
    (hi : ∀ x y, IsIso (F.map x y)) :
    QCatEquivalence (dgNerve A D) (dgNerve A (DGObjectImage F.obj)) :=
  dgObjectImageNerveEquivalence F
    (fun x y i => by
      let := hi x y
      exact (ConcreteCategory.bijective_of_isIso ((F.map x y).f i)).2)
    (fun x y => by let := hi x y; infer_instance)

end SerrePositivity.InfinityCategories
