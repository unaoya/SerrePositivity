module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingUpperPerfectDiagram
public import SerrePositivity.KST.SConstruction.DGPerfectRealizationPerfect
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingUpperTriangleRealization

/-!
概要：元上二単体全体の実 Perf 持ち上げを同じ第二段評価へ運ぶ。
方針：元実 Perf 図式を元 strict Perf realization で後合成する。
規約：元全二単体・元三境界を包含後に厳密回収する。
使われ方：同じ resolved 射影への全比較と固定 ν 上指定二単体。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded InfinityCategories
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
local notation "D" => dgIdentityHomGluingInverseRotationUpperPerfectDiagram R C F G a h
local notation "VP" => dgPerfectRealizationPerfect R C E J
local notation "V" => dgPerfectRealization R C E J

/-- 概要：元上二単体全体の同じ第二段 strict Perf 評価像。
方針：元全図式を元実 Perf 評価で後合成する。
規約：別の二単体を選ばない。使われ方：固定 ν 上面への元全図式。 -/
def dgIdentityHomGluingInverseRotationUpperPerfectRealizedDiagram :=
  (D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP)

/-- 概要：同じ第二段 Perf 図式は元上二単体の全実評価像を厳密回収する。
方針：元 strict 評価の包含則と元全二単体の包含回収を合成する。
規約：全図式の等号。使われ方：元三境界の同時照合。 -/
lemma dgIdentityHomGluingInverseRotationUpperPerfectRealizedDiagram_inclusion :
    dgIdentityHomGluingInverseRotationUpperPerfectRealizedDiagram R E C J F G a h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R E Set.univ) =
      uncurry (dgIdentityHomGluingInverseRotationUpperRealizedTriangle R E C J F G a h).diagram := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R E Set.univ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R C Set.univ) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (VP) _).symm.trans
      ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectRealizationPerfect_inclusion R C E J)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp _ (V)))
  change ((D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP)) ≫ _ = _
  rw [Category.assoc, hv, ← Category.assoc,
    dgIdentityHomGluingInverseRotationUpperPerfectDiagram_inclusion]
  exact (uncurry_natural_right
    (dgIdentityHomGluingInverseRotationUpperRawTriangle R C F G a h).diagram
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V))).symm
end SerrePositivity.KST.SConstruction
