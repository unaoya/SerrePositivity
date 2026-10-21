module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeWholeEdgeSquare
public import SerrePositivity.InfinityCategories.Stable.CoconeFamily

/-!
概要：同じ coslice 内の元の全余錐の族を、底を固定した全関手の族として表示する。
方針：既存の普遍余錐の族を使い、元の全余錐・底制限・頂点射影を回収する。
規約：元の coslice と全一単体を保持する。
使われ方：評価余錐と標準余極限余錐の一意比較を、両単位の可換正方形へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の同じ coslice の全余錐を、全関手の族へ写す。 -/
def nativeCoconeFunctorFamily {K X : SSet.{u}} (p : K ⟶ X) :
    sliceUnder p ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj X :=
  cosliceCoconeFamilyMap p ≫ vertexFiberι (coconeRestriction K X) (functorVertex p)

/-- 元の全余錐の族の底制限は、元の図式に厳密に定値。 -/
lemma nativeCoconeFunctorFamily_restriction {K X : SSet.{u}} (p : K ⟶ X) :
    nativeCoconeFunctorFamily p ≫ coconeRestriction K X = SSet.const (functorVertex p) := by
  rw [nativeCoconeFunctorFamily, Category.assoc, vertexFiberι_comp, SSet.comp_const]

/-- 元の全余錐の族の各頂点は、元の全余錐の射の同じ関手頂点。 -/
lemma nativeCoconeFunctorFamily_vertex {K X : SSet.{u}} {p : K ⟶ X} (q : JoinCocone p) :
    (nativeCoconeFunctorFamily p).app (Opposite.op ⦋0⦌) q = functorVertex q.val :=
  congrArg Subtype.val (cosliceCoconeFamilyMap_app_zero p q)

/-- 元の全余錐の族を右頂点で評価すると、元の coslice の頂点射影そのもの。 -/
lemma nativeCoconeFunctorFamily_apex {K X : SSet.{u}} (p : K ⟶ X) :
    nativeCoconeFunctorFamily p ≫ evaluateFunctorAt (coconeRightApexVertex K) =
      sliceUnderProjection p := by
  let S := sliceUnder p
  have hu : nativeCoconeFunctorFamily p = curry (cosliceCoconeFamilyUncurry p) := rfl
  rw [hu, curry_evaluateFunctorAt_vertex]
  have hl : lift (SSet.const (coconeRightApexVertex K)) (𝟙 S) =
      lift (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) (𝟙 S) ≫
        (joinInr K (Δ[0] : SSet.{u}) ▷ S) := by
    rw [lift_whiskerRight, SSet.const_comp]
    rfl
  change lift (SSet.const (coconeRightApexVertex K)) (𝟙 S) ≫
    joinTensorRight K Δ[0] S ≫ joinMap (𝟙 K) (snd Δ[0] S) ≫
      sliceUnderUncurry (𝟙 S) = _
  rw [hl, Category.assoc]
  rw [← Category.assoc (joinInr K Δ[0] ▷ S), joinTensorRight_inr]
  rw [← Category.assoc (joinInr K (Δ[0] ⊗ S)), joinInr_joinMap]
  rw [Category.assoc, sliceUnderUncurry_projection]
  simp only [← Category.assoc, lift_snd, Category.id_comp]

/-- 元の同じ coslice 内の辺を、元の全余錐の間の関手辺として表示する。 -/
def nativeCoconeFunctorEdge {K X : SSet.{u}} {p : K ⟶ X} {q d : JoinCocone p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (sliceUnder p)) q d) :
    SSet.Edge (functorVertex q.val) (functorVertex d.val) :=
  (SSet.Edge.ofTruncated (e.map ((truncation 2).map (nativeCoconeFunctorFamily p)))).ofEq
    (nativeCoconeFunctorFamily_vertex q) (nativeCoconeFunctorFamily_vertex d)

/-- 元の同じ coslice 辺の頂点成分は、元の頂点射影の同じ全一単体。 -/
lemma nativeCoconeFunctorEdge_apex {K X : SSet.{u}} {p : K ⟶ X} {q d : JoinCocone p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (sliceUnder p)) q d) :
    ((nativeCoconeFunctorEdge e).map (evaluateFunctorAt (coconeRightApexVertex K))).edge =
      (e.map ((truncation 2).map (sliceUnderProjection p))).edge :=
  congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e.edge) (nativeCoconeFunctorFamily_apex p)

/-- 同じ元の coslice 辺の底変換は、元の底図式の恒等辺と同じ全一単体。 -/
lemma nativeCoconeFunctorEdge_bottom_id {K X : SSet.{u}} {p : K ⟶ X}
    {q d : JoinCocone p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (sliceUnder p)) q d) :
    (coconeWholeEdgeBottom q d (nativeCoconeFunctorEdge e).toTruncated).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj X)) (functorVertex p)).edge :=
  congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e.edge) (nativeCoconeFunctorFamily_restriction p)

/-- 元の coslice 辺での全余錐比較は、元の変換と同じ頂点変換の後合成を与える。 -/
lemma nativeCoconeFunctorEdge_unit_square {K X : SSet.{u}} {p : K ⟶ X}
    {q d : JoinCocone p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (sliceUnder p)) q d) :
    SSet.Truncated.HomotopyCategory.homMk
      (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex d)).toTruncated =
    SSet.Truncated.HomotopyCategory.homMk
      (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex q)).toTruncated ≫
    SSet.Truncated.HomotopyCategory.homMk
      (coconeWholeEdgeTop q d (nativeCoconeFunctorEdge e).toTruncated).toTruncated := by
  have h := coconeWholeEdge_square q d (nativeCoconeFunctorEdge e).toTruncated
  have hi : (coconeWholeEdgeBottom q d (nativeCoconeFunctorEdge e).toTruncated).toTruncated =
      SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj X)) (functorVertex p) := by
    apply SSet.Truncated.Edge.ext
    exact nativeCoconeFunctorEdge_bottom_id e
  rw [hi, SSet.Truncated.HomotopyCategory.homMk_id, Category.id_comp] at h
  exact h

end SerrePositivity.InfinityCategories.HomotopyLimits
