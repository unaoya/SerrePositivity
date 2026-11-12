module
public import SerrePositivity.KST.SConstruction.PerfectSemiorthogonalInvariant
public import SerrePositivity.KST.LocalizingInvariants.VertexIsoPath

/-! # 同じ半直交分解の値の実 ∞ 積と可逆辺
概要：証明した積分解を、実 Sp 積の極限錐と元の中央値への可逆辺として保持する。
方針：同じ実 fiber 列の積錐と、同じ分裂同型の類を持つ可逆辺を用いる。
規約：群の積や任意の同型へ置き換えない。使われ方：Tamme の Sp 値分裂。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 元の BF スペクトルの同じ単体的圏を使う。 -/
local instance perfectSemiorthogonalSplit_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

variable {E : perfectStableInfinity.{u} ⟶ Sp.{u}} (hE : IsPerfectLocalizingInvariant E)
  {a b t : perfectStableInfinity.{u} _⦋0⦌} (d : PerfectSemiorthogonalDecomposition a b t)

/-- 同じ積分解の射の類を持つ、元の中央値への実 Sp の辺。 -/
def IsPerfectLocalizingInvariant.perfectSemiorthogonalSplitEdge : Sp.{u}.Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (NativeSplit.product
      (hE.sequenceFiberTriangle (perfectSemiorthogonalVerdierSequence d))))
    (E.app (Opposite.op ⦋0⦌) (perfectSemiorthogonalVerdierSequence d).middleVertex) :=
  VertexIsoPath.edge (hE.perfectSemiorthogonalSplitEquivalence d)

/-- 同じ分裂の辺は、実 Sp における可逆辺。 -/
lemma IsPerfectLocalizingInvariant.perfectSemiorthogonalSplitEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (hE.perfectSemiorthogonalSplitEdge d).toTruncated :=
  VertexIsoPath.edge_invertible (hE.perfectSemiorthogonalSplitEquivalence d)

/-- 実可逆辺の射の類は、元の三射を回収する同じ積分解の射そのもの。 -/
lemma IsPerfectLocalizingInvariant.perfectSemiorthogonalSplitEdge_hom :
    Truncated.HomotopyCategory.homMk (hE.perfectSemiorthogonalSplitEdge d).toTruncated =
      (hE.perfectSemiorthogonalSplitEquivalence d).hom :=
  VertexIsoPath.edge_hom (hE.perfectSemiorthogonalSplitEquivalence d)

/-- 分裂の同じ実可逆辺の終点は、元の中央頂点の不変量値そのもの。 -/
lemma IsPerfectLocalizingInvariant.perfectSemiorthogonalSplitEdge_target :
    Sp.δ 0 (hE.perfectSemiorthogonalSplitEdge d).edge = E.app (Opposite.op ⦋0⦌) t :=
  (hE.perfectSemiorthogonalSplitEdge d).tgt_eq.trans
    (congrArg (fun x => E.app (Opposite.op ⦋0⦌) x)
      (perfectSemiorthogonalVerdierSequence_vertices d).2.1)

/-- 同じ分裂の二因子による実 Sp の積錐。 -/
def IsPerfectLocalizingInvariant.perfectSemiorthogonalProductCone :=
  NativeSplit.productCone (hE.sequenceFiberTriangle (perfectSemiorthogonalVerdierSequence d))

/-- 同じ実積錐は、Sp の ∞ 極限である。 -/
lemma IsPerfectLocalizingInvariant.perfectSemiorthogonalProductCone_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (hE.perfectSemiorthogonalProductCone d) :=
  NativeSplit.productCone_isLimit _

/-- 同じ実積錐の頂点は、分裂可逆辺の始点に使った元の BF 積。 -/
lemma IsPerfectLocalizingInvariant.perfectSemiorthogonalProductCone_vertex :
    (hE.perfectSemiorthogonalProductCone d).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (NativeSplit.product
        (hE.sequenceFiberTriangle (perfectSemiorthogonalVerdierSequence d))) :=
  NativeSplit.productCone_vertex _

end SerrePositivity.KST.SConstruction
