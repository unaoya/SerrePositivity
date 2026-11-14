module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictUnderlyingComparison
public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictRestrictionComparison

/-!
# BE 制限と同じ台の忘却の全関手比較

概要：HA §4.2.1–§4.2.3 の制限が同じ台の忘却と整合することを示す。
方針：出力解像度・台の評価の全関手比較を使い、一対象での評価を照合する。
規約：対象ごとの同値で済ませない。使われ方：変わる底の加群族の同じ忘却。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
variable {A : Type u} [CommRing A]

/-- 概要：同じ一対象での制限後の dg 評価は元の評価（HA §4.2.3）。
方針：制限 Hom の評価公式を適用する。
規約：全 Hom の等式。使われ方：台の忘却の全関手比較。 -/
lemma strictRestriction_evaluation {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    (dgModuleRestriction A _ _ (dgAlgebraMap A ((assocForget A).map f)).op).comp
      (moduleEvaluationDG A (dgAlgebraCategory A ((assocForget A).obj X))
        (Opposite.op DGAlgebraPoint.star)) =
      moduleEvaluationDG A (dgAlgebraCategory A ((assocForget A).obj Y))
        (Opposite.op DGAlgebraPoint.star) := by
  refine EnrichedFunctor.ext (Complex A) ?_ ?_
  · intro M
    rfl
  intro M T
  simp only [EnrichedFunctor.comp_map, eqToHom_refl, Category.comp_id]
  change moduleRestrictionHom A _ _ _ M T ≫ moduleHomπ A _ _ _ _ = _
  rw [moduleRestrictionHom_π]
  rfl

/-- 概要：指定制限後の台と元の台の忘却は全関手同型（HA §4.2.3）。
方針：指定解像度の因数分解と唯一点評価の等式で同じ D(A) への二関手を比較する。
規約：射影性保存や平坦性は不要。使われ方：BE 加群族の忘却の整合性。 -/
def strictModuleRestrict_underlyingIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso (strictModuleRestrict f ≫ strictModuleUnderlying A X)
      (strictModuleUnderlying A Y) := by
  let D := dgAlgebraCategory A ((assocForget A).obj X)
  let E := dgAlgebraCategory A ((assocForget A).obj Y)
  let I := semifreeInclusion A E
  let R := dgModuleRestriction A D E (dgAlgebraMap A ((assocForget A).map f)).op
  let VD := moduleEvaluationDG A D (Opposite.op DGAlgebraPoint.star)
  let VE := moduleEvaluationDG A E (Opposite.op DGAlgebraPoint.star)
  let Q := dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
    (semifreePointEquivalence A).hom
  have raw : FunctorIso (strictModuleRestrict f) (N I ≫ N R ≫ moduleResolution A D) := by
    change FunctorIso (dgModuleResolvedInfinity A _ D (I.comp R)) _
    have h := dgModuleResolvedInfinity_rawFactorIso A (SemifreeDGModules A E) D (I.comp R)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at h
    exact h
  have eX : FunctorIso ((N I ≫ N R ≫ moduleResolution A D) ≫ strictModuleUnderlying A X)
      (N I ≫ N R ≫ N VD ≫ Q) := by
    simpa only [Category.assoc] using
      (strictModuleResolvedUnderlyingIso A X).precomp (N I ≫ N R)
  have ret : FunctorIso (N I ≫ moduleResolution A E ≫ strictModuleUnderlying A Y)
      (strictModuleUnderlying A Y) := by
    simpa only [Category.assoc, Category.id_comp] using
      (dgModuleResolutionRetractIso A E).postcomp (strictModuleUnderlying A Y)
  have eY : FunctorIso (strictModuleUnderlying A Y) (N I ≫ N VE ≫ Q) :=
    ret.symm ≪≫ (strictModuleResolvedUnderlyingIso A Y).precomp (N I)
  have ev : N R ≫ N VD = N VE := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
    exact congrArg N (strictRestriction_evaluation f)
  have e : FunctorIso (strictModuleRestrict f ≫ strictModuleUnderlying A X)
      (N I ≫ N R ≫ N VD ≫ Q) := raw.postcomp (strictModuleUnderlying A X) ≪≫ eX
  rw [← Category.assoc (N R) (N VD), ev] at e
  exact e ≪≫ eY.symm

end SerrePositivity.EInfinity.BarrattEccles
