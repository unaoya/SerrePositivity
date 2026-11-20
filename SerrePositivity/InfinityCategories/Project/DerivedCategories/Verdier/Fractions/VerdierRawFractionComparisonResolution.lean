module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFractionComparisonResolution
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.GroupoidCompletionKanComparison

/-!
概要：完成分数の比較経路を保持したまま、元の実分数の全族へ戻す。
方針：完成分数射影を元の亜群化単位に沿って引き戻し、同じ可換四角形で比較する。
規約：完成分数への比較は局所化同型。任意の境界の厳密持ち上げ性は主張しない。
使われ方：実分母・分子を持つ族と、完成分数の比較経路を接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x y : B.obj _⦋0⦌)

instance verdierFractionComparisonResolution_quasicategory :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierFractionComparisonResolution h x y) := by
  change Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement _)
  infer_instance

/-- 同じ完成分数を元の実分数として回収する、比較経路付き引き戻し。 -/
def verdierRawFractionComparisonResolution : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierFractionComparisonResolutionRoof h x y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y))

/-- 元の分母と分子を持つ実 span 族を回収する。 -/
def verdierRawFractionComparisonResolutionRoof :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolution h x y ⟶
      fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y :=
  pullback.snd _ _

/-- 比較経路と、その同じ完成分数を回収する。 -/
def verdierRawFractionComparisonResolutionCompleted :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolution h x y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierFractionComparisonResolution h x y :=
  pullback.fst _ _

/-- 両方の射影は、同じ完成分数の全単体で厳密に一致する。 -/
lemma verdierRawFractionComparisonResolution_square :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionCompleted h x y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierFractionComparisonResolutionRoof h x y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionRoof h x y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) :=
  pullback.condition

/-- 実分数への射影は、元の実分数の任意の指定部分族を保持して充填できる。 -/
instance verdierRawFractionComparisonResolutionRoof_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionRoof h x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

instance verdierRawFractionComparisonResolution_quasicategory :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolution h x y) :=
  quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionRoof h x y)

/-- 記憶した同じ比較経路の商側終点。 -/
def verdierRawFractionComparisonResolutionMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolution h x y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionCompleted h x y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierFractionComparisonResolutionMap h x y

/-- 全パラメータでの実分数評価と、記憶した商側の族を結ぶ同じ比較。 -/
def verdierRawFractionComparisonResolutionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionRoof h x y ≫
      fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionMap h x y) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionMappingComparisonIso q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionRoof h x y)
  have f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierFractionComparisonResolutionIso h x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionCompleted h x y)
  have he : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionRoof h x y ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionMappingComparison q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionCompleted h x y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierFractionComparisonResolutionRoof h x y ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionMappingComparison q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y) := by
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolution_square,
      Category.assoc]
  rw [he] at e
  exact e ≪≫ f

/-- 実分母と実分子の全 span 図式。完成分数の頂点からの非自然な選択は使わない。 -/
def verdierRawFractionComparisonResolutionSpan :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolution h x y ⟶
      (ihom (horn 2 0 : SSet.{u})).obj B.obj :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionRoof h x y ≫
    fixedMarkedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y ≫
      markedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)

/-- 回収した全族の各実分母は、元の Verdier 弱同値集合に属する。 -/
lemma verdierRawFractionComparisonResolutionSpan_denominator_mem
    (v : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolution h x y) _⦋0⦌) :
    spanLeftEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionSpan h x y).app
      (Opposite.op ⦋0⦌) v) ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionRoof h x y ≫
      fixedMarkedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y).app
        (Opposite.op ⦋0⦌) v)

/-- 完成分数側への比較は、同じ亜群化単位と二つの実自明射影により局所化同型。 -/
lemma verdierRawFractionComparisonResolutionCompleted_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionCompleted h x y)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hp : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionRoof h x y)) :=
    homotopyEquivalence_anodyneQ_isIso _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence
  have hc : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierFractionComparisonResolutionRoof h x y)) :=
    homotopyEquivalence_anodyneQ_isIso _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence
  have hu := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.groupoidCompletionUnit_anodyneQ_isIso
    (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)
  have he := congrArg (fun f => Q.map f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolution_square h x y)
  rw [Q.map_comp, Q.map_comp] at he
  have hh : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionCompleted h x y) ≫
      Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierFractionComparisonResolutionRoof h x y)) := he.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hh

/-- 実分数と同じ比較経路を保持する終点評価も、元の anodyne 局所化で可逆。 -/
lemma verdierRawFractionComparisonResolutionMap_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionMap h x y)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRawFractionComparisonResolutionCompleted_localized_isIso h x y
  have hm : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierFractionComparisonResolutionMap h x y)) :=
    homotopyEquivalence_anodyneQ_isIso _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence
  change IsIso (Q.map (_ ≫ _))
  rw [Q.map_comp]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
