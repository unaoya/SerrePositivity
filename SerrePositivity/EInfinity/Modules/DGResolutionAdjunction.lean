module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.DGModuleResolutionLocalization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGUniversalCounitInterval
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleStrictNatTrans
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.IntervalEndpointTransport
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CounitMappingAdjunction

/-!
# 半自由包含と同じ実加群解像度の随伴

概要：HA §1.3.1 の半自由模型の包含は、指定した全関手的解像度を右随伴に持つ。
方針：同じ増大に Hom を適用し、半自由加群の射影性から全写像空間の普遍性を得る。
規約：準同型を生の dg nerve 内で可逆とは見なさない。
使われ方：HA §4.2.3 の graph 延長・制限の導来随伴の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open scoped Simplicial
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：元の半自由全包含（HA §1.3.1）。
方針：全 Hom を変えずに含める。規約：同じ実 dg 関手。
使われ方：解像度の余単位。 -/
abbrev semifreeInclusion :=
  dgFullSubcategoryInclusion A (RightModule A D) (dgModuleSemifreeProperty A D)

/-- 概要：元の全加群に対する指定実解像度（HA §1.3.1）。
方針：恒等加群値関手の出力解像度を使う。規約：同じ全単体の関手。
使われ方：半自由包含の右随伴。 -/
abbrev moduleResolution :=
  dgModuleResolvedInfinity A (RightModule A D) D (DGFunctor.id (RightModule A D))

/-- 概要：包含の余単位列は元の加群 Hom の後合成（HA §1.3.1）。
方針：全次数の斉次射で包含と閉後合成を評価する。
規約：同じ閉加群射。使われ方：射影性による普遍性。 -/
lemma semifreeCounitColumn_eq (P T : SemifreeDGModules A D) (M : RightModule A D)
    (ε : ForgetEnrichment.of (Complex A) P.val ⟶ ForgetEnrichment.of (Complex A) M) :
    dgCounitColumn A (SemifreeDGModules A D) (RightModule A D) (semifreeInclusion A D)
      (closedHomEquiv A (RightModule A D)
        (ForgetEnrichment.of (Complex A) ((semifreeInclusion A D).obj P))
        (ForgetEnrichment.of (Complex A) M) ε) T =
    moduleHomPostcompose A D T.val P.val M ε := by
  apply chain_ext_apply
  intro n z
  change compose A (closedHomEquiv A (RightModule A D) _ _ ε).val z (add_zero n) = _
  exact (dgModuleHomPostcompose_apply A D ε z).symm

/-- 概要：半自由解像度の同じ増大は全 Hom で普遍（HA §1.3.1）。
方針：半自由入力の射影性で増大への Hom が準同型となる。
規約：元の加群は射影的でなくてよい。使われ方：native な包含・解像度随伴。 -/
def semifreeUniversalCounit (P : SemifreeDGModules A D) (M : RightModule A D)
    (ε : ForgetEnrichment.of (Complex A) P.val ⟶ ForgetEnrichment.of (Complex A) M)
    (hε : moduleQuasiIso A D ε) :
    DGUniversalCounit A (SemifreeDGModules A D) (RightModule A D) (semifreeInclusion A D) M where
  source := P
  counit := ε
  quasiIso T := by
    rw [semifreeCounitColumn_eq A D P T M ε]
    exact moduleHomotopicallyProjective_postcompose_quasiIso A D
      (dgSemifreeModule_isProjective A D T) ε hε

/-- 概要：同じ実解像度の頂点値は指定した半自由 replacement（HA §1.3.1）。
方針：dg nerve の頂点同値で両辺を回収する。
規約：対象ごとの別選択はしない。使われ方：増大の端点の照合。 -/
lemma moduleResolution_vertex (M : RightModule A D) :
    (moduleResolution A D).app (Opposite.op ⦋0⦌) (Simplex.vertex (A := A) M) =
      Simplex.vertex (A := A) (dgModuleOutputResolutionObject A (RightModule A D) D
        (DGFunctor.id (RightModule A D)) M).replacement := by
  apply (Simplex.vertexEquiv (A := A) (D := SemifreeDGModules A D)).injective
  rfl

/-- 概要：同じ半自由包含と指定解像度の native 随伴（HA §1.3.1）。
方針：指定増大の全区間写像空間条件から両三角恒等式を得る。
規約：全関手圏での随伴。使われ方：graph 随伴と解像度付き制限の比較。 -/
def moduleResolutionAdjunction :
    QCatAdjunction (N (semifreeInclusion A D)) (moduleResolution A D) := by
  apply qcatAdjunctionOfCounitIntervalCondition (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.dgModuleResolutionAugmentationHomotopy A D)
  intro x y
  obtain ⟨P, rfl⟩ := (Simplex.vertexEquiv (A := A) (D := SemifreeDGModules A D)).symm.surjective x
  obtain ⟨M, rfl⟩ := (Simplex.vertexEquiv (A := A) (D := RightModule A D)).symm.surjective y
  let Q := dgModuleOutputResolutionObject A (RightModule A D) D (DGFunctor.id (RightModule A D)) M
  let e := semifreeUniversalCounit A D Q.replacement Q.source Q.augmentation Q.quasiIso
  exact intervalFunctorPostcompose_equivalence_of_endpoint
    (N (semifreeInclusion A D)) (Simplex.vertex (A := A) P)
    ((moduleResolution A D).app (Opposite.op ⦋0⦌) (Simplex.vertex (A := A) M)) (Simplex.vertex (A := A) Q.replacement)
    (simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.dgModuleResolutionAugmentationHomotopy A D) (Simplex.vertex (A := A) M))
    (SSet.Edge.ofTruncated (dgClosedEdge A (RightModule A D) Q.augmentation))
    (moduleResolution_vertex A D M)
    (dgFunctorNerve_vertex (semifreeInclusion A D) P)
    (dgFunctorNerve_vertex (semifreeInclusion A D) Q.replacement)
    (congrArg (fun X : RightModule A D => Simplex.vertex (A := A) X)
      (dgModuleOutputResolutionObject_source A (RightModule A D) D (DGFunctor.id (RightModule A D)) M).symm)
    (dgModuleResolvedAugmentationHomotopy_vertex_edge A (RightModule A D) D
      (DGFunctor.id (RightModule A D)) M)
    (e.nativeIntervalMap_isSimplicialHomotopyEquivalence P)

end SerrePositivity.EInfinity.Modules
