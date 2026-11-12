module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedKan
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.EdgeHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Paths
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-! # 右 pinched 写像空間の π₀ と H⁰ の射

概要：dg nerve の右 pinched 写像空間の連結成分は dg 圏の H⁰ の射と同値。
方針：道を右辺ホモトピー、さらに境界関係に同定し、頂点の対応を π₀ に降ろす。
規約：Kerodon §4.6.5（Tag 01KW）、HA Example 1.3.1.8。使われ方：導来 ∞ 圏の写像空間の連結成分。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：写像空間の頂点は既存の閉零圏の射と同値。
方針：元の端点付き辺との同値を、N3 の閉零射との同値に合成する。
規約：HA Example 1.3.1.8、Kerodon §4.6.5（Tag 01KW）。使われ方：π₀ 比較の代表元の写像。 -/
def vertexClosedEquiv (x y : D) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋0⦌ ≃
    (ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeClosedEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))

/-- 概要：写像空間で道があることは、対応する閉零射の境界関係と同値。
方針：道を右辺ホモトピーに読み替え、N3 の比較と境界関係の対称性を使う。
規約：Kerodon §4.6.5（Tag 01KW）、HA Example 1.3.1.8。使われ方：π₀ 上の写像とその単射性。 -/
lemma path_iff_boundary {x y : D} (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋0⦌) :
    Nonempty ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y).Edge s t) ↔
      boundaryRelation A D (vertexClosedEquiv x y s) (vertexClosedEquiv x y t) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.path_iff_compStruct]
  change SSet.Truncated.HomotopicR
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv _ _ t).toTruncated)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv _ _ s).toTruncated) ↔ _
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.homotopicR_iff_boundary]
  change boundaryRelation A D (vertexClosedEquiv x y t) (vertexClosedEquiv x y s) ↔ _
  exact ⟨fun ⟨h⟩ => ⟨h.symm⟩, fun ⟨h⟩ => ⟨h.symm⟩⟩

/-- 概要：写像空間の連結成分を H⁰ の射へ送る。
方針：頂点を閉零射の境界類に送り、各道が境界関係となることから π₀ の普遍性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：連結成分の比較同値の順写像。 -/
def piZeroToH0 (x y : D) : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) →
    ((toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x) ⟶
      (toHomotopy A D).obj (ForgetEnrichment.of (Complex A) y)) :=
  SSet.π₀.lift (fun s => (toHomotopy A D).map (vertexClosedEquiv x y s))
    (fun _ _ e => (toHomotopy_map_eq_iff A D _ _).mpr ((path_iff_boundary _ _).mp ⟨e⟩))

/-- 概要：連結成分の比較は頂点の代表元を対応する閉零射の境界類に送る。
方針：π₀ の持ち上げを代表元で評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：比較の単射性・全射性と具体計算。 -/
lemma piZeroToH0_mk {x y : D} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋0⦌) :
    piZeroToH0 x y (SSet.π₀.mk s) = (toHomotopy A D).map (vertexClosedEquiv x y s) := rfl

/-- 概要：写像空間の二頂点の連結成分が等しいことは閉零射の境界関係と同値。
方針：順方向は H⁰ への写像、逆方向は境界関係から作る一本の道で示す。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：連結成分の比較の単射性。 -/
lemma piZero_mk_eq_iff_boundary {x y : D} (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋0⦌) :
    SSet.π₀.mk s = SSet.π₀.mk t ↔
      boundaryRelation A D (vertexClosedEquiv x y s) (vertexClosedEquiv x y t) := by
  constructor
  · intro h
    apply (toHomotopy_map_eq_iff A D _ _).mp
    exact congrArg (piZeroToH0 x y) h
  · intro h
    obtain ⟨e⟩ := (path_iff_boundary s t).mpr h
    exact SSet.π₀.sound e

/-- 概要：π₀ から H⁰ の射への比較は単射。
方針：連結成分の頂点代表元を選び、H⁰ の等式を境界関係、次いで π₀ の等式へ戻す。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：比較同値の構成。 -/
lemma piZeroToH0_injective (x y : D) : Function.Injective (piZeroToH0 (A := A) x y) := by
  intro s t h
  obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective s
  obtain ⟨t, rfl⟩ := SSet.π₀.mk_surjective t
  exact (piZero_mk_eq_iff_boundary s t).mpr ((toHomotopy_map_eq_iff A D _ _).mp h)

/-- 概要：π₀ から H⁰ の射への比較は全射。
方針：H⁰ の閉零代表元を選び、頂点と閉零射の同値の逆で頂点代表元を作る。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：比較同値の構成。 -/
lemma piZeroToH0_surjective (x y : D) : Function.Surjective (piZeroToH0 (A := A) x y) := by
  intro f
  obtain ⟨g, hg⟩ := (toHomotopy A D).map_surjective f
  refine ⟨SSet.π₀.mk ((vertexClosedEquiv x y).symm g), ?_⟩
  rw [piZeroToH0_mk, Equiv.apply_symm_apply]
  exact hg

/-- 概要：右 pinched 写像空間の π₀ は dg 圏の H⁰ の Hom と同値。
方針：代表元を閉零射の境界類へ送る比較の単射性と全射性をまとめる。
規約：Kerodon §4.6.5（Tag 01KW）、HA Example 1.3.1.8。使われ方：写像空間の連結成分の同定。 -/
def piZeroEquiv (x y : D) : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) ≃
    ((toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x) ⟶
      (toHomotopy A D).obj (ForgetEnrichment.of (Complex A) y)) :=
  Equiv.ofBijective (piZeroToH0 x y) ⟨piZeroToH0_injective x y, piZeroToH0_surjective x y⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
