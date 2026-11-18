module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteTotFunctorCone
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DerivedNatTransIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LimitConeVertexTransport

/-!
概要：元のweighted Totセルの全図式射・全高次単体の評価族。
方針：既存StrictSimplexCategoryと全評価を、元の指定セルと厳密写像へ適用。
規約：IS-W2 D01の既存構成の組み立て・表示則。同じ元の全joinセルへ戻す。
使われ方：HA 1.2.4、全錐族の局所セルの貼り合わせ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 標準零単体の射影で定値化した全関手のcurryの零セルは、同じ関手頂点。 -/
theorem discreteTotFunctorVertex_curry_fst {B D : SSet.{u+1}} (F : B ⟶ D) :
    SSet.yonedaEquiv (curry (fst B (Δ[0] : SSet.{u+1}) ≫ F)) = functorVertex F := by
  rfl

/-- 元のraw離散全錐の頂点は同じ全積Tot関手。 -/
theorem rawDiscreteTotFunctorCone_vertex :
    (rawDiscreteTotFunctorCone A).vertex =
      functorVertex (nerveMap (discreteTotalFunctor A) ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) := by
  rw [JoinCone.vertex_eq, rawDiscreteTotFunctorCone, ← curry_natural_left]
  have he :
      (nerve (CosimplicialObject (ModuleCat.{u} A)) ◁
        joinInl (Δ[0] : SSet.{u+1})
          ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))) ≫ (β_ _ _).hom ≫
        (𝟙 _ ⊗ₘ nerveMap (discreteDiagramFunctor A)) =
      (β_ _ _).hom ≫ (𝟙 (Δ[0] : SSet.{u+1}) ⊗ₘ nerveMap (discreteDiagramFunctor A)) ≫
        (joinInl (Δ[0] : SSet.{u+1})
          ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
            𝟙 (nerve (CosimplicialObject (Complex A)))) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro τ
    rfl
  have h := congrArg (· ≫ derivedTotConeFamily A) he
  simp only [Category.assoc] at h
  rw [derivedTotConeFamily_left] at h
  simp only [tensorHom_snd_assoc, braiding_hom_snd_assoc] at h
  have hc := congrArg (fun k => SSet.yonedaEquiv (curry k)) h
  rw [discreteTotFunctorVertex_curry_fst] at hc
  exact hc

/-- 同じ自然同型を全通常導来入口へ移した、交代余面から積Totへの全関手同型。 -/
def discreteTotCochainDerivedIso :
    FunctorIso (nerveMap (discreteCochainFunctor A) ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)
      (nerveMap (discreteTotalFunctor A) ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) :=
  _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransIso A (discreteTotalCochainNatIso A).inv
    (fun M => by infer_instance)

/-- 全関手圏で同じ自然同型に沿って頂点を移すと、同じ交代余面頂点の極限錐が得られる。 -/
theorem exists_discreteCochainFunctorCone :
    ∃ c : JoinCone (rawDiscreteTotFunctorDiagram A), IsLimitCone c ∧
      c.vertex = functorVertex (nerveMap (discreteCochainFunctor A) ≫
        _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) := by
  let e := (discreteTotCochainDerivedIso A).edge
  let f : SSet.Edge
      (functorVertex (nerveMap (discreteCochainFunctor A) ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A))
      (rawDiscreteTotFunctorCone A).vertex :=
    ⟨e.edge, e.src_eq, e.tgt_eq.trans (rawDiscreteTotFunctorCone_vertex A).symm⟩
  have hf : SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge f := by
    exact (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (show f.edge = (discreteTotCochainDerivedIso A).edge.edge from rfl)).2
        (discreteTotCochainDerivedIso A).edge_isInvertible
  exact exists_limitCone_vertex_of_invertible (rawDiscreteTotFunctorCone A)
    (rawDiscreteTotFunctorCone_isLimit A) f hf

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
