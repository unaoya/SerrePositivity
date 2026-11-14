module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeCellApex
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeCocone

/-!
概要：元の native 余錐セルの全族を、同じ前面と同じ apex を持つ全余錐族へ貼り合わせる。
方針：全パラメーターの関手単体集合の slice に各セルを入れ、既存の slice 普遍性を使う。
規約：元の全 HA 成分と前面・apex の全関手比較を使う。
使われ方：3b-3 R6、元の実現と native apex の全関手比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 全パラメーターを保った元の strict 図式を、関手単体集合の図式として読む。 -/
def strictBarNativeFunctorDiagram : ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) ⟶ (ihom (nerve (J ⥤ ModuleCategory A PUnit.{1}))).obj (dgNerve A (RightModule A PUnit.{1})) :=
  curry ((strictModuleCoherentFamily A J (𝟭 (J ⥤ ModuleCategory A PUnit.{1}))).evaluation)

/-- 全パラメーターに共通な同じ正規化 bar の apex 関手の零セル。 -/
def strictBarNativeFunctorApex : (Δ[0] : SSet.{u + 1}) ⟶ (ihom (nerve (J ⥤ ModuleCategory A PUnit.{1}))).obj (dgNerve A (RightModule A PUnit.{1})) :=
  curry (strictBarApexCellEvaluation A J)

/-- 同じ前面と固定 apex 関手を持つ、元の native 余錐セルの全族。 -/
def strictBarNativeFunctorOverSimplex {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    (sliceOver (strictBarNativeFunctorApex A J)) _⦋n⦌ := by
  refine ⟨(joinStdSimplexIso n 0).hom ≫ curry (strictBarNativeCellEvaluation A J s), ?_⟩
  change joinInr (Δ[n] : SSet.{u + 1}) Δ[0] ≫
    ((joinStdSimplexIso n 0).hom ≫ curry (strictBarNativeCellEvaluation A J s)) =
      curry (strictBarApexCellEvaluation A J)
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_inr,
    ← curry_natural_left, strictBarNativeCellEvaluation_apex]

/-- U04の証明の分割：元の全セルの自然性を固定した二つの次元で計算する。 -/
lemma strictBarNativeFunctorOverSimplex_naturality {m n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (joinStdSimplexIso m 0).hom ≫ curry (strictBarNativeCellEvaluation A J
      (((SSet.uliftFunctor.{u, 0}).obj (nerve J)).map α.op s)) =
    joinMap (SSet.stdSimplex.map α) (𝟙 Δ[0]) ≫
      ((joinStdSimplexIso n 0).hom ≫ curry (strictBarNativeCellEvaluation A J s)) := by
  have hc := strictBarNativeCellEvaluation_pullback A J s α.toOrderHom
  change strictBarNativeCellEvaluation A J
      (((SSet.uliftFunctor.{u, 0}).obj (nerve J)).map α.op s) =
    (nerve (J ⥤ ModuleCategory A PUnit.{1}) ◁
      SSet.stdSimplex.map (SimplexCategory.mkHom (extendOrderHom α.toOrderHom))) ≫
        strictBarNativeCellEvaluation A J s at hc
  have hj : (joinStdSimplexIso m 0).hom ≫
      SSet.stdSimplex.map (SimplexCategory.mkHom (extendOrderHom α.toOrderHom)) =
      joinMap (SSet.stdSimplex.map α) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
        (joinStdSimplexIso n 0).hom :=
    (joinStdSimplexIso_rightPoint_naturality.{u + 1} α).symm
  rw [hc, curry_natural_left, ← Category.assoc, hj, Category.assoc]

/-- 同じ全族の native セルは、全面・退化に自然な slice の切断を与える。 -/
def strictBarNativeFunctorOverSection :
    ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) ⟶
      sliceOver (strictBarNativeFunctorApex A J) where
  app n := ↾fun s => strictBarNativeFunctorOverSimplex A J (n := n.unop.len) s.down
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact strictBarNativeFunctorOverSimplex_naturality A J s.down α.unop

/-- 同じ slice 切断の前面は、元の全 strict 図式の関手単体集合での図式と一致する。 -/
lemma strictBarNativeFunctorOverSection_projection :
    strictBarNativeFunctorOverSection A J ≫ sliceOverProjection (strictBarNativeFunctorApex A J) =
      strictBarNativeFunctorDiagram A J := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  change SSet.yonedaEquiv (joinInl (Δ[n] : SSet.{u + 1}) Δ[0] ≫
      ((joinStdSimplexIso n 0).hom ≫ curry (strictBarNativeCellEvaluation A J s))) = _
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_inl, ← curry_natural_left]
  have hf := strictBarNativeCellEvaluation_front A J s
  change (nerve (J ⥤ ModuleCategory A PUnit.{1}) ◁ SSet.stdSimplex.map (front n)) ≫
      strictBarNativeCellEvaluation A J s = _ at hf
  rw [hf, curry_natural_left, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- 全セルを同じ前面・apex のまま貼り合わせた、関手単体集合での元の全余錐族。 -/
def strictBarNativeFunctorCocone : JoinCocone (strictBarNativeFunctorDiagram A J) :=
  ⟨sliceOverUncurry (strictBarNativeFunctorOverSection A J), by
    rw [sliceOverUncurry_projection, strictBarNativeFunctorOverSection_projection]⟩

/-- 元の全パラメーターと join の全単体を同時に評価する native 余錐の族。 -/
def strictBarNativeJoinFamily : (nerve (J ⥤ ModuleCategory A PUnit.{1})) ⊗ join ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1}) ⟶ (dgNerve A (RightModule A PUnit.{1})) :=
  uncurry (strictBarNativeFunctorCocone A J).val

/-- 全余錐族の前面は、元の同じ全 strict 図式の評価に厳密に一致する。 -/
lemma strictBarNativeJoinFamily_front :
    ((nerve (J ⥤ ModuleCategory A PUnit.{1})) ◁ joinInl ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1})) ≫ strictBarNativeJoinFamily A J =
      (strictModuleCoherentFamily A J (𝟭 (J ⥤ ModuleCategory A PUnit.{1}))).evaluation := by
  rw [strictBarNativeJoinFamily, ← uncurry_natural_left,
    (strictBarNativeFunctorCocone A J).property]
  exact uncurry_curry _

/-- 全余錐族の apex も、同じ全パラメーターの正規化 bar の評価に一致する。 -/
lemma strictBarNativeJoinFamily_apex :
    ((nerve (J ⥤ ModuleCategory A PUnit.{1})) ◁ joinInr ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1})) ≫ strictBarNativeJoinFamily A J =
      strictBarApexCellEvaluation A J := by
  rw [strictBarNativeJoinFamily, strictBarNativeFunctorCocone, ← uncurry_natural_left,
    sliceOverUncurry_fixed]
  exact uncurry_curry _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
