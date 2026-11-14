module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationUpperNative
public import SerrePositivity.KST.SConstruction.DGPerfectRealization
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorTrianglePostcomposition

/-!
概要：元包含・負符号・指定逆回転比較を持つ元上二単体を実 realization で運ぶ。
方針：同じ元全二単体を同じ tensor 評価でそのまま後合成する。
規約：三辺から別の二単体を選ばず、元負符号付き長辺を保持する。
使われ方：元実上二単体の二段評価と固定 ν 接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  (J : DGFunctor R C (PerfectDGModule R E))
  {P : Type (max (u + 1) v)} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
/-- 概要：元指定上二単体の同じ実 tensor 評価像。
方針：元の全二単体を同じ native realization 射で後合成する。
規約：元包含・指定逆・負符号付き長辺を保持。
使われ方：元全実逆回転上二単体の実評価側。 -/
def dgIdentityHomGluingInverseRotationUpperRealizedTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.postcomposeFunctorCompositionTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectRealization R C E J))
    (dgIdentityHomGluingInverseRotationUpperRawTriangle R C F G a h)

/-- 概要：元上二単体の realization は元全二単体の同じ後合成。
方針：元二単体の後合成定義を回収する。
規約：辺だけでなく全二単体を保持。使われ方：元指定上二単体の prism 接続。 -/
lemma dgIdentityHomGluingInverseRotationUpperRealizedTriangle_diagram :
    (dgIdentityHomGluingInverseRotationUpperRealizedTriangle R E C J F G a h).diagram =
      (dgIdentityHomGluingInverseRotationUpperRawTriangle R C F G a h).diagram ≫
        (CategoryTheory.ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P)).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectRealization R C E J)) := rfl
end SerrePositivity.KST.SConstruction
