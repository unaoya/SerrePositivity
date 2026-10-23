module
public import SerrePositivity.KST.SConstruction.DGKFixedInterface
public import SerrePositivity.KST.SConstruction.DGFunctorClosedNativeEdge
public import SerrePositivity.InfinityCategories.F1.Coherent.EnrichedHomotopy
public import SerrePositivity.InfinityCategories.F1.Universe.InvertibleEdge
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalVertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalFatDiagram

/-! # 固定 dg 入力 S の同じ二辺を元の Hom end の閉同型から比較する
概要：指定された閉 dg 関手同型の辺を、同じ固定 S の豊穣 Hom に持ち上げる。
方針：同じ native core 辺の持ち上げから h の等号と指定三辺の実二単体を得る。
規約：二単体の選択と ν 像の追加照合は区別。使われ方：具体的 ⊙ の cone 作用の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] {P Q : PerfDGInput.{u, v} R}

/-- 固定 S の通常射の豊穣頂点は、同じ元の厳密 dg 関手の native 頂点。 -/
lemma dgKInputHom_vertex (f : P ⟶ Q) :
    SimplicialCategory.homEquiv' P Q f =
      ULift.up (dgFunctorNativeMappingVertex R P Q f.down) := by
  change SSet.unitHomEquiv _ (perfDGInputUnitHomEquiv R P Q f) = _
  exact perfDGInputUnitHomEquiv_vertex R P Q f

variable (f g : P ⟶ Q)
  (e : ForgetEnrichment.of (Complex R) f.down ≅ ForgetEnrichment.of (Complex R) g.down)
include e

/-- 元の Hom end の同じ閉順射を、固定 S の同じ実 Hom の辺へ持ち上げる。 -/
def dgKInputClosedIsoHomEdge :
    (SimplicialCategory.sHom P Q).Edge
      (SimplicialCategory.homEquiv' P Q f) (SimplicialCategory.homEquiv' P Q g) := by
  rw [dgKInputHom_vertex, dgKInputHom_vertex]
  change ((SSet.uliftFunctor.{u + 1, max u v}).obj
    (dgFunctorNativeMappingSpace R P Q)).Edge
      (ULift.up (dgFunctorNativeMappingVertex R P Q f.down))
      (ULift.up (dgFunctorNativeMappingVertex R P Q g.down))
  exact SSet.Edge.ofTruncated
    (uliftTruncatedEdge (dgFunctorClosedIsoNativeEdge R P Q f.down g.down e).toTruncated)

/-- 元の実 Hom end の同型を持つ二辺は、同じ固定 S の h で等しい。 -/
lemma dgKInputClosedIso_homMk_eq :
    Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated =
      Truncated.HomotopyCategory.homMk (coherentNerveEdge g).toTruncated := by
  let a := dgKInputClosedIsoHomEdge R f g e
  have : IsIso (Truncated.HomotopyCategory.homMk a.toTruncated) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (SimplicialCategory.sHom P Q)) _
  exact coherentNerveEdge_homMk_eq_of_enrichedVertexIso
    (asIso (Truncated.HomotopyCategory.homMk a.toTruncated))

/-- 同じ指定 native 辺を、標準 coherent 区間 Hom 比較でそのまま写す。 -/
def dgKInputClosedIsoIntervalEdge :
    (intervalMappingSpace (coherentNerveVertex P) (coherentNerveVertex Q)).Edge
      (intervalMappingVertexOfEdge (coherentNerveEdge f))
      (intervalMappingVertexOfEdge (coherentNerveEdge g)) := by
  let a : ((SSet.uliftFunctor).obj (SimplicialCategory.sHom P Q)).Edge
      (ULift.up (SimplicialCategory.homEquiv' P Q f))
      (ULift.up (SimplicialCategory.homEquiv' P Q g)) :=
    Edge.ofTruncated (uliftTruncatedEdge (dgKInputClosedIsoHomEdge R f g e).toTruncated)
  exact (a.map (coherentHomIntervalComparison P Q)).ofEq
    (by rw [coherentHomIntervalComparison_vertex, Equiv.symm_apply_apply])
    (by rw [coherentHomIntervalComparison_vertex, Equiv.symm_apply_apply])

/-- 元の native 辺の標準区間比較全体。三角形の充填を選び直さない実四角形。 -/
def dgKInputClosedIsoSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ dgKInputInfinity.{u, v} R :=
  intervalMappingUncurry (SSet.yonedaEquiv.symm (dgKInputClosedIsoIntervalEdge R f g e).edge)

/-- 同じ標準比較四角形の始域端は、元の固定 S の始点に定値。 -/
lemma dgKInputClosedIsoSquare_zero :
    prismEndpoint 0 (Δ[1]) ≫ dgKInputClosedIsoSquare R f g e =
      SSet.const (coherentNerveVertex P) :=
  intervalMappingUncurry_zero _

/-- 同じ標準比較四角形の終域端は、元の固定 S の終点に定値。 -/
lemma dgKInputClosedIsoSquare_one :
    prismEndpoint 1 (Δ[1]) ≫ dgKInputClosedIsoSquare R f g e =
      SSet.const (coherentNerveVertex Q) :=
  intervalMappingUncurry_one _

/-- 同じ固定 S の指定二辺と恒等辺を持つ実比較二単体を選ぶ。 -/
def dgKInputClosedIsoTriangle :
    Edge.CompStruct (coherentNerveEdge f) (coherentNerveEdge (𝟙 Q))
      (coherentNerveEdge g) := by
  refine Edge.CompStruct.ofTruncated (compStruct_nonempty_of_homMk_fac ?_).some
  erw [coherentNerveEdge_id, Edge.toTruncated_id, Truncated.HomotopyCategory.homMk_id,
    Category.comp_id]
  exact dgKInputClosedIso_homMk_eq R f g e

/-- 同じ選択済みの比較二単体全体を、固定 ν に写す。 -/
def dgKInputClosedIsoNuTriangle :
    Edge.CompStruct ((coherentNerveEdge f).map (dgKInputNu R))
      ((coherentNerveEdge (𝟙 Q)).map (dgKInputNu R))
      ((coherentNerveEdge g).map (dgKInputNu R)) :=
  (dgKInputClosedIsoTriangle R f g e).map (dgKInputNu R)

/-- 同じ選択済みの比較二単体全体を、固定 K に写す。 -/
def dgKInputClosedIsoKTriangle :
    Edge.CompStruct ((coherentNerveEdge f).map (dgKInputK R))
      ((coherentNerveEdge (𝟙 Q)).map (dgKInputK R))
      ((coherentNerveEdge g).map (dgKInputK R)) :=
  (dgKInputClosedIsoTriangle R f g e).map (dgKInputK R)

end SerrePositivity.KST.SConstruction
