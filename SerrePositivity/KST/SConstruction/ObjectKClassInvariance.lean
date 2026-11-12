module
public import SerrePositivity.KST.SConstruction.SOneObjectClasses

/-! # 対象の実際の K 類の同型不変性
概要：元の BF K 群の対象類は可逆な辺とホモトピー圏の同型で不変になる。
方針：可逆な辺を core の辺とし、元の core の連結成分で検出する。
規約：群と loop は構成済みのものを使う。使われ方：TriangulatedK0 の同型関係の確認。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open Spectra
open scoped Simplicial

/-- 同じ core の連結成分にある二対象は同じ元の K loop の類を与える。 -/
lemma objectKPiZeroClass_eq_of_coreClass_eq (X : StableModel.{u}) (x y : X.carrier _⦋0⦌)
    (h : SSet.π₀.mk (objectCoreVertex X x) = SSet.π₀.mk (objectCoreVertex X y)) :
    objectKPiZeroClass X x = objectKPiZeroClass X y := by
  unfold objectKPiZeroClass
  rw [h]

/-- 同じ core の連結成分にある二対象は同じ実際の BF K 類を与える。 -/
lemma objectKClass_eq_of_coreClass_eq (X : StableModel.{u}) (x y : X.carrier _⦋0⦌)
    (h : SSet.π₀.mk (objectCoreVertex X x) = SSet.π₀.mk (objectCoreVertex X y)) :
    objectKClass X x = objectKClass X y := by
  unfold objectKClass
  rw [objectKPiZeroClass_eq_of_coreClass_eq X x y h]

/-- 元の可逆な一単体の両端の対象の K 類は一致する。 -/
lemma objectKClass_invertibleSimplex (X : StableModel.{u}) (s : X.carrier _⦋1⦌)
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s)) :
    objectKClass X (X.carrier.δ 1 s) = objectKClass X (X.carrier.δ 0 s) := by
  let t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X.carrier : SSet.{u}) _⦋1⦌ :=
    ⟨s, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff s).mpr hs⟩
  apply objectKClass_eq_of_coreClass_eq
  exact SSet.π₀.sound (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex t))

/-- 元の端点を明示した可逆辺に沿って対象の BF K 類は不変。 -/
lemma objectKClass_invertibleEdge (X : StableModel.{u}) {x y : X.carrier _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X.carrier) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) : objectKClass X x = objectKClass X y := by
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e.edge) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := e) (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e.edge) rfl).mp he
  have h := objectKClass_invertibleSimplex X e.edge hs
  have hx : X.carrier.δ 1 e.edge = x := e.src_eq
  have hy : X.carrier.δ 0 e.edge = y := e.tgt_eq
  rw [hx, hy] at h
  exact h

/-- ホモトピー圏で同型な元の二頂点の BF K 類は一致する。 -/
lemma objectKClass_iso (X : StableModel.{u}) {x y : X.carrier _⦋0⦌}
    (e : SSet.HomotopyCategory.mk (X := X.carrier) x ≅ SSet.HomotopyCategory.mk y) :
    objectKClass X x = objectKClass X y := by
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y e.hom
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk a)
    rw [ha]
    infer_instance
  exact objectKClass_invertibleEdge X a hi

/-- ホモトピー圏の対象から実際の加法記法の零次 K 群への対象類。 -/
def homotopyObjectKClass (X : StableModel.{u}) (a : hoFunctor.obj X.carrier) :
    Additive (OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0) := objectKClass X a.as.as

/-- ホモトピー圏の頂点表示での対象類は元の対象の類。 -/
lemma homotopyObjectKClass_mk (X : StableModel.{u}) (x : X.carrier _⦋0⦌) :
    homotopyObjectKClass X (SSet.HomotopyCategory.mk x) = objectKClass X x := rfl

/-- ホモトピー圏の任意の二対象の同型は実際の BF K 類を保つ。 -/
lemma homotopyObjectKClass_iso (X : StableModel.{u}) {a b : hoFunctor.obj X.carrier} (e : a ≅ b) :
    homotopyObjectKClass X a = homotopyObjectKClass X b := by
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
  exact objectKClass_iso X e

end SerrePositivity.KST.SConstruction
