module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullIntervalComponent
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullTrianglePrismDiagonalIntervals
/-!
概要：元上下三角形の対角比較は、同じ実両端固定区間 Hom で同じ射の類を持つ。
方針：元二対角を可縮な零成分の同じ実頂点として回収し、充満忠実な比較を使う。
規約：元実／絶対二対角と元全ホモトピーを保持する。
使われ方：片方の全三角形比較の代表を、他方の対角に厳密に合わせる。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
/-- 概要：同じ元実対角を零区間 Hom 成分の実頂点として保持する。
方針：同じ元零 Hom 頂点の宇宙持ち上げを全次数同型で移す。
規約：元の完全射。使われ方：実区間対角比較の固定始点。 -/
def dgOdotMilnorNuNullDiagonalIntervalComponentVertex :
    (DGOdotMilnorNuNullIntervalComponent R d) _⦋0⦌ :=
  (dgOdotMilnorNuNullIntervalComponentIso R d h).hom.app (Opposite.op ⦋0⦌)
    (ULift.up (dgOdotMilnorNuNullDiagonalVertex R d))
/-- 概要：同じ元絶対対角を零区間 Hom 成分の実頂点として保持する。
方針：同じ元絶対零 Hom 頂点を全次数同型で移す。
規約：元の完全射。使われ方：実区間対角比較の固定終点。 -/
def dgOdotMilnorNuAbsoluteDiagonalIntervalComponentVertex :
    (DGOdotMilnorNuNullIntervalComponent R d) _⦋0⦌ :=
  (dgOdotMilnorNuNullIntervalComponentIso R d h).hom.app (Opposite.op ⦋0⦌)
    (ULift.up (dgOdotMilnorNuAbsoluteDiagonalVertex R d h))
/-- 概要：元零成分の実始点の像は元実対角辺の実区間頂点。
方針：同じ Hom 頂点と標準 coherent 比較の頂点式を照合する。
規約：頂点の厳密等号。使われ方：元両端を保つ対角比較の一意性。 -/
lemma dgOdotMilnorNuNullDiagonalIntervalComponentVertex_map :
    (dgOdotMilnorNuNullIntervalComponentMap R d).app (Opposite.op ⦋0⦌)
        (dgOdotMilnorNuNullDiagonalIntervalComponentVertex R d h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuNullDiagonalMap R d)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B)).app _
    (ULift.up ((dgOdotMilnorNuNullCoherenceHom R d h).app _
      (dgOdotMilnorNuNullDiagonalVertex R d))) = _
  rw [dgOdotMilnorNuNullDiagonalComparison_source]
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1})
    (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1})
      (K) (B) (dgOdotMilnorNuNullDiagonalMap R d))
  exact he.trans (congrArg
    (fun f : (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) ⟶ (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) f))
    (Equiv.symm_apply_apply
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1})
        (K) (B)) (dgOdotMilnorNuNullDiagonalMap R d)))
/-- 概要：元零成分の実終点の像は元絶対対角辺の実区間頂点。
方針：同じ元絶対 Hom 頂点と標準比較の頂点式を照合する。
規約：頂点の厳密等号。使われ方：同じ実終点を保つ射の類の比較。 -/
lemma dgOdotMilnorNuAbsoluteDiagonalIntervalComponentVertex_map :
    (dgOdotMilnorNuNullIntervalComponentMap R d).app (Opposite.op ⦋0⦌)
        (dgOdotMilnorNuAbsoluteDiagonalIntervalComponentVertex R d h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuAbsoluteDiagonalMap R d h)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B)).app _
    (ULift.up ((dgOdotMilnorNuNullCoherenceHom R d h).app _
      (dgOdotMilnorNuAbsoluteDiagonalVertex R d h))) = _
  rw [dgOdotMilnorNuNullDiagonalComparison_target]
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1})
    (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1})
      (K) (B) (dgOdotMilnorNuAbsoluteDiagonalMap R d h))
  exact he.trans (congrArg
    (fun f : (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) ⟶ (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) f))
    (Equiv.symm_apply_apply
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1})
        (K) (B)) (dgOdotMilnorNuAbsoluteDiagonalMap R d h)))
/-- 概要：元下全比較から得た元両端固定の実区間対角辺。
方針：同じ元対角パラメーターの二面を実端点として読む。
規約：元の一単体。使われ方：共有対角の代表修正。 -/
def dgOdotMilnorNuNullLowerDiagonalIntervalEdge : SSet.Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuNullDiagonalMap R d)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuAbsoluteDiagonalMap R d h))) where
  edge := SSet.yonedaEquiv (dgOdotMilnorNuNullLowerDiagonalIntervalParameter R d h)
  src_eq := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (K)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (B))).δ 1
      (SSet.yonedaEquiv (dgOdotMilnorNuNullLowerDiagonalIntervalParameter R d h)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuNullDiagonalMap R d))
    have he := congrArg SSet.yonedaEquiv
      (dgOdotMilnorNuNullLowerDiagonalIntervalParameter_faces R d h).1
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using he
  tgt_eq := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (K)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (B))).δ 0
      (SSet.yonedaEquiv (dgOdotMilnorNuNullLowerDiagonalIntervalParameter R d h)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuAbsoluteDiagonalMap R d h))
    have he := congrArg SSet.yonedaEquiv
      (dgOdotMilnorNuNullLowerDiagonalIntervalParameter_faces R d h).2
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using he
/-- 概要：元上全比較から得た同じ元両端固定の実区間対角辺。
方針：同じ元上対角パラメーターの二面を読む。
規約：元の一単体。使われ方：元下対角を厳密に合わせる指定代表。 -/
def dgOdotMilnorNuNullUpperDiagonalIntervalEdge : SSet.Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuNullDiagonalMap R d)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuAbsoluteDiagonalMap R d h))) where
  edge := SSet.yonedaEquiv (dgOdotMilnorNuNullUpperDiagonalIntervalParameter R d h)
  src_eq := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (K)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (B))).δ 1
      (SSet.yonedaEquiv (dgOdotMilnorNuNullUpperDiagonalIntervalParameter R d h)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuNullDiagonalMap R d))
    have he := congrArg SSet.yonedaEquiv
      (dgOdotMilnorNuNullUpperDiagonalIntervalParameter_faces R d h).1
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using he
  tgt_eq := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (K)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (B))).δ 0
      (SSet.yonedaEquiv (dgOdotMilnorNuNullUpperDiagonalIntervalParameter R d h)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuAbsoluteDiagonalMap R d h))
    have he := congrArg SSet.yonedaEquiv
      (dgOdotMilnorNuNullUpperDiagonalIntervalParameter_faces R d h).2
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using he
/-- 概要：元上下対角比較は同じ実両端固定区間 Hom のホモトピー圏で一致する。
方針：元の零成分の二頂点の像の間の Hom の一意性を使う。
規約：元の二実一単体。使われ方：全三角形比較の類を保つ厳密な代表修正。 -/
lemma dgOdotMilnorNuNullDiagonalIntervalEdge_homMk_eq :
    SSet.Truncated.HomotopyCategory.homMk
        (dgOdotMilnorNuNullLowerDiagonalIntervalEdge R d h).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk
        (dgOdotMilnorNuNullUpperDiagonalIntervalEdge R d h).toTruncated := by
  have hu := dgOdotMilnorNuNullIntervalComponentMap_hom_ext R d h
    (dgOdotMilnorNuNullDiagonalIntervalComponentVertex R d h)
    (dgOdotMilnorNuAbsoluteDiagonalIntervalComponentVertex R d h)
  rw [dgOdotMilnorNuNullDiagonalIntervalComponentVertex_map,
    dgOdotMilnorNuAbsoluteDiagonalIntervalComponentVertex_map] at hu
  exact hu _ _
end SerrePositivity.KST.SConstruction
