module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFSOASpectrumComparison
public import SerrePositivity.KST.SConstruction.DGKappaNativeCoherentBFArrowComparison
public import SerrePositivity.KST.Spectra.CoherentNerve

/-!
概要：同じ I の旧 K 対象と新 BF 対象を Sp 内の実頂点同型で結ぶ。
方針：同じ全段比較から修正した実スペクトル弱同値の可逆辺を使う。
規約：四辺の全写像空間比較を要求しない。使われ方：K-B の実核と実商の構造辺の接続。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories NonConnective Spectra Fibration
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

local instance nativeBFVertexComparisonTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 概要：同じ実スペクトル比較の整数 π 作用は既公開の指定群比較そのもの。
方針：修正が保持する正段の基点固定成分を標準段で評価する。
規約：同じ全整数の指定比較。使われ方：既存の新旧四辺の群比較との整合。 -/
lemma dgKappaNativeBFSOASpectrumComparison_homotopyMap_eq
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (j : ℤ) :
    OmegaSpectrum.homotopyMap (dgKappaNativeBFSOASpectrumComparison.{u, v} R D I C) j =
      dgKappaNativeBFIntegerComparison.{u, v} R D I C j := by
  apply MonoidHom.ext
  intro a
  have hc : PointedMapping.componentOf
      ((dgKappaNativeBFSOASpectrumComparison.{u, v} R D I C).app (j.natAbs + 1)) =
        PointedMapping.componentOf
          (dgKappaNativeBFPositiveLevelComparison.{u, v} R D I C j.natAbs) :=
    dgKappaNativeBFSOASpectrumComparison_component.{u, v} R D I C (j.natAbs + 1)
  have hm := congrFun (pointedHomotopyMap_eq_of_component hc
    (OmegaSpectrum.degree j (OmegaSpectrum.canonicalLevel j))) a
  exact (OmegaSpectrum.homotopyMap_apply
    (dgKappaNativeBFSOASpectrumComparison.{u, v} R D I C) j a).trans
      (hm.trans (dgKappaNativeBFIntegerComparison_apply.{u, v} R D I C j a).symm)

/-- 概要：同じ旧 K から新 BF への実比較辺は Sp で可逆。
方針：同じ実スペクトル比較の全整数 π 同型を使う。
規約：抽象群同型だけから推論しない。使われ方：実頂点同型。 -/
lemma dgKappaNativeBFSOASpectrumComparison_isInvertible
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (dgKappaNativeBFSOASpectrumComparison.{u, v} R D I C)).toTruncated :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (dgKappaNativeBFSOASpectrumComparison_piIsomorphism.{u, v} R D I C)

/-- 概要：同じ有限 native 対象の旧 K と新 BF の実 Sp 頂点同型。
方針：同じ実比較スペクトル射の可逆辺をホモトピー圏の同型へ束ねる。
規約：対象と辺を選び直さない。使われ方：同じ実核・実商の接続。 -/
def dgKappaNativeBFSOAVertexIso (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum (sInputModel C.obj)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C)) :=
  @asIso _ _ _ _ (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFSOASpectrumComparison.{u, v} R D I C)).toTruncated)
    (dgKappaNativeBFSOASpectrumComparison_isInvertible.{u, v} R D I C)

/-- 概要：同じ I の実核 c=0 と実商 c=3 の旧 K と新 BF は Sp 内で実際に同型。
方針：同じ有限 native 二頂点で構成済みの実比較同型を使う。
規約：四辺の Sp 写像空間比較は要求しない。使われ方：K-B の S3 補足入力。 -/
theorem dgKappaNativeBFKernelQuotientVertexIso (c : Fin 4) (_ : c = 0 ∨ c = 3) :
    let C := dgKappaNativeBFFiniteNativeObject.{u, v} R D I c
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum (sInputModel C.obj)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C))) :=
  ⟨dgKappaNativeBFSOAVertexIso.{u, v} R D I
    (dgKappaNativeBFFiniteNativeObject.{u, v} R D I c)⟩

end SerrePositivity.KST.SConstruction
