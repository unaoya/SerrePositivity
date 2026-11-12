module
public import SerrePositivity.KST.NonConnective.DGKappaNativeSquareComparison
public import SerrePositivity.KST.Fibration.SpectrumSpaceEvaluation
public import SerrePositivity.KST.SConstruction.KSpectrumMaps
public import SerrePositivity.KST.SConstruction.PointedSOAExInfinityComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanWhiteheadComparison

/-!
概要：D-9 の同じ未完備 native 四角形の全正段と元 BF 頂点の比較を固定する。
方針：元の全二胞体を豊穣境界商関手で写し、同じ単射置換射影を使用する。
規約：この一四角形だけを扱い、全正段の比較から Sp 四角形の存在を推論しない。
使われ方：元の kSpectrumMap 四辺を保つ有限 BF 四角形の構成。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open LocalizingInvariants Fibration NonConnective Spectra
open scoped Simplicial
local instance nativeBFStagesSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ未完備 native 実四角形の全二胞体を保つ正段像。
方針：同じ元四角形へ既存の全 Hom 関手を適用する。
規約：Perf 値へ置換しない。使われ方：要求された全正段比較の右辺。 -/
def dgKappaNativeBFStageSquare (r : ℕ) :
    (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v} :=
  (dgKappaNativeVerdierDiagram.{u, v} R D I).square ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableBoundaryClosedKanEnrichedFunctor.{max (u + 1) v} r)

/-- 概要：同じ native 四角形の四頂点の元の安定圏。
方針：元四角形の頂点から回収する。
規約：冪等完備化しない。使われ方：元 BF 頂点と元境界商の照合。 -/
def dgKappaNativeBFVertexCategory (a b : Fin 2) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaNativeVerdierDiagram.{u, v} R D I).square a b)

/-- 概要：同じ未完備四頂点の元の BF スペクトル。
方針：既存の同じ kOmegaSpectrum を使用する。
規約：新しい BF 模型を選ばない。使われ方：有限 Sp 四角形の頂点。 -/
def dgKappaNativeBFVertexSpectrum (a b : Fin 2) : OmegaSpectrum.{max (u + 1) v} :=
  kOmegaSpectrum (sInputModel (dgKappaNativeBFVertexCategory.{u, v} R D I a b))

/-- 概要：同じ四頂点の元 BF 正段から元 SOA 境界商への射影。
方針：同じ単射置換の射影をそのまま使う。
規約：同じ未完備の値を保つ。使われ方：Ex∞ 比較の前の指定射影。 -/
def dgKappaNativeBFSOAProjection (a b : Fin 2) (r : ℕ) :
    (((dgKappaNativeBFVertexSpectrum.{u, v} R D I a b).level (r + 1)).space).right ⟶
      (((kKanSequence (sInputModel (dgKappaNativeBFVertexCategory.{u, v} R D I a b))).level
        (r + 1)).space).right :=
  ((monicKKanSequenceProjection
    (sInputModel (dgKappaNativeBFVertexCategory.{u, v} R D I a b))).app (r + 1)).right

/-- 概要：同じ四頂点の元 SOA 射影は全単射持ち上げ性を持つ。
方針：元の同じ射影の性質を特殊化する。
規約：Ex∞ 比較後に持ち上げ性を主張しない。使われ方：境界を保つ段射の延長。 -/
lemma dgKappaNativeBFSOAProjection_rlp (a b : Fin 2) (r : ℕ) :
    (MorphismProperty.monomorphisms SSet.{max (u + 1) v}).rlp
      (dgKappaNativeBFSOAProjection.{u, v} R D I a b r) :=
  monicKKanSequenceProjection_rlp
    (sInputModel (dgKappaNativeBFVertexCategory.{u, v} R D I a b)) (r + 1)

/-- 概要：元 BF 正段から同じ元境界商の Ex∞ 値への指定前向き比較。
方針：元の置換射影と元の SOA・Ex∞ 比較を合成する。
規約：二つの Kan 模型を同一視しない。使われ方：全図式比較の四頂点成分。 -/
def dgKappaNativeBFPositiveProjection (a b : Fin 2) (r : ℕ) :
    (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1)).obj
      (dgKappaNativeBFVertexSpectrum.{u, v} R D I a b) ⟶
    (stableBoundaryClosedKanEnrichedFunctor.{max (u + 1) v} r).obj
      (dgKappaNativeBFVertexCategory.{u, v} R D I a b) := by
  change (((dgKappaNativeBFVertexSpectrum.{u, v} R D I a b).level (r + 1)).space).right ⟶
    ((exInfinityPointedKanEnrichedFunctor.obj (stableBoundaryPointedObject r
      (dgKappaNativeBFVertexCategory.{u, v} R D I a b))).obj).right
  exact dgKappaNativeBFSOAProjection.{u, v} R D I a b r ≫
    (pointedSOAExInfinityComparison
      (stableBoundaryPointedObject r (dgKappaNativeBFVertexCategory.{u, v} R D I a b))).right

/-- 概要：元 BF 正段から Ex∞ 境界商への同じ前向き比較は全基点 π 同型。
方針：元の二つの比較の全基点 π 同型を合成する。
規約：指定された同じ比較。使われ方：四頂点成分の可逆性。 -/
lemma dgKappaNativeBFPositiveProjection_piIsomorphism (a b : Fin 2) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (dgKappaNativeBFPositiveProjection.{u, v} R D I a b r) :=
  (monicKKanSequenceProjection_piIsomorphism
    (sInputModel (dgKappaNativeBFVertexCategory.{u, v} R D I a b)) (r + 1)).comp
      (pointedSOAExInfinityComparison_piIsomorphism
        (stableBoundaryPointedObject r (dgKappaNativeBFVertexCategory.{u, v} R D I a b)))

/-- 概要：元の正段射影は SpaceInfinity の同じ可逆辺を与える。
方針：合成比較の全基点 π 同型を既存の Kan 同値判定へ渡す。
規約：指定射影そのものを保持する。使われ方：有限全図式比較の頂点成分。 -/
lemma dgKappaNativeBFPositiveProjection_isInvertible (a b : Fin 2) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFPositiveProjection.{u, v} R D I a b r)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.homotopyEquivalence_of_kanPiIsomorphism_of_vertex
    (dgKappaNativeBFPositiveProjection.{u, v} R D I a b r)
    (dgKappaNativeBFPositiveProjection_piIsomorphism.{u, v} R D I a b r)
    (((dgKappaNativeBFVertexSpectrum.{u, v} R D I a b).level (r + 1)).space).basepoint
  exact he.isQCatEquivalence

end SerrePositivity.KST.SConstruction
