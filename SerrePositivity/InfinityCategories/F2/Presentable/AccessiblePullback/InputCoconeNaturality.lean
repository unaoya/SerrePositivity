module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.InputCoconeValue
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.InputRestrictionProjection

/-!
概要：既存の入力頂点からの相対余錐の全値の自然性を証明する。
方針：既存の三因子式と join の自然性を使い、全後合成と全制限を追跡する。
規約：relativeSliceCocone の同じ全余錐を扱う。
使われ方：成分の追加入力の下の余錐を元の pullback の余錐と合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
open HomotopyLimits

/-- 概要：既存の入力頂点余錐の基底全値は元の頂点族の基底先端余錐。
方針：既存の相対余錐の全射影公式を使う。
規約：元の入力を保つ全余錐値の等式。
使われ方：元の compact 成分頂点条件の回収。 -/
lemma inputVertexSliceCocone_projection {K X : SSet.{u}} {x : (Δ[0] : SSet.{u}) ⟶ X}
    (U : K ⟶ sliceOver x)
    (v : (sliceOver ((SSet.yonedaEquiv
      (X := sliceUnder (U ≫ sliceOverProjection x))).symm (sliceDiagramCocone U))) _⦋0⦌) :
    (inputVertexSliceCocone U v).val ≫ sliceOverProjection x =
      ((sliceOverProjection ((SSet.yonedaEquiv
        (X := sliceUnder (U ≫ sliceOverProjection x))).symm (sliceDiagramCocone U))).app
          (Opposite.op ⦋0⦌) v).val := by
  dsimp only [inputVertexSliceCocone]
  exact relativeSliceCocone_projection U _

/-- 概要：既存の入力頂点余錐の先端は元の頂点族の二重基底射影。
方針：同じ全基底余錐値の等式を頂点で評価する。
規約：先端は厳密な等式で回収する。
使われ方：元の compact 成分頂点条件の回収。 -/
lemma inputVertexSliceCocone_vertex_projection {K X : SSet.{u}} {x : (Δ[0] : SSet.{u}) ⟶ X}
    (U : K ⟶ sliceOver x)
    (v : (sliceOver ((SSet.yonedaEquiv
      (X := sliceUnder (U ≫ sliceOverProjection x))).symm (sliceDiagramCocone U))) _⦋0⦌) :
    (sliceOverProjection x).app (Opposite.op ⦋0⦌) (inputVertexSliceCocone U v).vertex =
      ((sliceOverProjection ((SSet.yonedaEquiv
        (X := sliceUnder (U ≫ sliceOverProjection x))).symm (sliceDiagramCocone U)) ≫
          sliceUnderProjection (U ≫ sliceOverProjection x)).app (Opposite.op ⦋0⦌) v) := by
  let w : JoinCocone (U ≫ sliceOverProjection x) :=
    (sliceOverProjection ((SSet.yonedaEquiv
      (X := sliceUnder (U ≫ sliceOverProjection x))).symm (sliceDiagramCocone U))).app
        (Opposite.op ⦋0⦌) v
  have hc : mapJoinCocone (sliceOverProjection x) (inputVertexSliceCocone U v) = w :=
    Subtype.ext (inputVertexSliceCocone_projection U v)
  have hv := congrArg (fun d : JoinCocone (U ≫ sliceOverProjection x) ↦ d.vertex) hc
  rw [Ind.mapJoinCocone_vertex] at hv
  exact hv

/-- 概要：全入力頂点の底での後合成等式は、既存の元の slice 余錐の後合成等式を与える。
方針：元の余錐の全展開公式で両辺を比較する。
規約：元の全入力付き頂点の値を取り替えない。
使われ方：元の pullback 余錐の成分全値を追加入力側へ合わせる。 -/
lemma inputVertexSliceCocone_postcomp_val {K X Y : SSet.{u}}
    {x : (Δ[0] : SSet.{u}) ⟶ X} (f : X ⟶ Y)
    (U : K ⟶ sliceOver x) (V : K ⟶ sliceOver (x ≫ f))
    (v : (sliceOver ((SSet.yonedaEquiv
      (X := sliceUnder (U ≫ sliceOverProjection x))).symm (sliceDiagramCocone U))) _⦋0⦌)
    (w : (sliceOver ((SSet.yonedaEquiv
      (X := sliceUnder (V ≫ sliceOverProjection (x ≫ f)))).symm (sliceDiagramCocone V))) _⦋0⦌)
    (h : sliceUnderUncurry v.val ≫ f = sliceUnderUncurry w.val) :
    (inputVertexSliceCocone U v).val ≫ sliceOverPostcomp x f = (inputVertexSliceCocone V w).val := by
  apply sliceOverUncurry_injective (x ≫ f)
  rw [sliceOverUncurry_postcomp, inputVertexSliceCocone_uncurry,
    inputVertexSliceCocone_uncurry, Category.assoc, h]

/-- 概要：全入力頂点の始域制限等式は元の slice 余錐の全制限等式を与える。
方針：三因子再結合の自然性と元の全展開公式を使う。
規約：入力全体の高次単体の等式を保つ。
使われ方：指定始点を含む入力の余錐を元の入力の余錐へ制限する。 -/
lemma inputVertexSliceCocone_restrict_val {K L X : SSet.{u}}
    {x : (Δ[0] : SSet.{u}) ⟶ X} (i : K ⟶ L)
    (U : L ⟶ sliceOver x) (V : K ⟶ sliceOver x)
    (v : (sliceOver ((SSet.yonedaEquiv
      (X := sliceUnder (U ≫ sliceOverProjection x))).symm (sliceDiagramCocone U))) _⦋0⦌)
    (w : (sliceOver ((SSet.yonedaEquiv
      (X := sliceUnder (V ≫ sliceOverProjection x))).symm (sliceDiagramCocone V))) _⦋0⦌)
    (h : joinMap i (𝟙 (join Δ[0] Δ[0])) ≫ sliceUnderUncurry v.val = sliceUnderUncurry w.val) :
    joinMap i (𝟙 Δ[0]) ≫ (inputVertexSliceCocone U v).val = (inputVertexSliceCocone V w).val := by
  apply sliceOverUncurry_injective x
  rw [sliceOverUncurry_precomp, inputVertexSliceCocone_uncurry, inputVertexSliceCocone_uncurry]
  have hn := joinAssociator_naturality i (𝟙 (Δ[0] : SSet.{u})) (𝟙 (Δ[0] : SSet.{u}))
  rw [joinMap_id] at hn
  rw [← Category.assoc, hn, Category.assoc, h]

/-- 概要：成分後合成と追加入力制限が全頂点値で一致すれば元の全余錐でも一致する。
方針：既存の全値公式を三因子再結合の自然性で比較する。
規約：指定始点を含む入力全体の等式を使う。
使われ方：元の pullback 余錐と追加入力付き成分余錐の厳密な貼り合わせ。 -/
lemma inputVertexSliceCocone_postcomp_restrict_val {K L X Y : SSet.{u}}
    {x : (Δ[0] : SSet.{u}) ⟶ X} (f : X ⟶ Y) (i : K ⟶ L)
    (U : K ⟶ sliceOver x) (V : L ⟶ sliceOver (x ≫ f))
    (v : (sliceOver ((SSet.yonedaEquiv
      (X := sliceUnder (U ≫ sliceOverProjection x))).symm (sliceDiagramCocone U))) _⦋0⦌)
    (w : (sliceOver ((SSet.yonedaEquiv
      (X := sliceUnder (V ≫ sliceOverProjection (x ≫ f)))).symm (sliceDiagramCocone V))) _⦋0⦌)
    (h : sliceUnderUncurry v.val ≫ f =
      joinMap i (𝟙 (join Δ[0] Δ[0])) ≫ sliceUnderUncurry w.val) :
    (inputVertexSliceCocone U v).val ≫ sliceOverPostcomp x f =
      joinMap i (𝟙 Δ[0]) ≫ (inputVertexSliceCocone V w).val := by
  apply sliceOverUncurry_injective (x ≫ f)
  rw [sliceOverUncurry_postcomp, sliceOverUncurry_precomp,
    inputVertexSliceCocone_uncurry, inputVertexSliceCocone_uncurry]
  have hn := joinAssociator_naturality i (𝟙 (Δ[0] : SSet.{u})) (𝟙 (Δ[0] : SSet.{u}))
  rw [joinMap_id] at hn
  rw [← Category.assoc, hn, Category.assoc, Category.assoc, h]

/-- 概要：元の余錐の成分全値が別の余錐の入力制限なら先端の成分も一致する。
方針：全値の等式を余錐の最終点に制限する。
規約：先端は同型ではなく厳密に一致する。
使われ方：追加入力側の先端の compact 性を元の成分から回収する。 -/
lemma cocone_vertex_image_eq_of_val_eq_restrict {K L X Y : SSet.{u}}
    {U : K ⟶ X} {V : L ⟶ Y} (f : X ⟶ Y) (i : K ⟶ L)
    (c : JoinCocone U) (d : JoinCocone V)
    (h : c.val ≫ f = joinMap i (𝟙 Δ[0]) ≫ d.val) :
    f.app (Opposite.op ⦋0⦌) c.vertex = d.vertex := by
  have hv := congrArg (fun g ↦ SSet.yonedaEquiv (joinInr K Δ[0] ≫ g)) h
  change (mapJoinCocone f c).vertex = (d.restrict i).vertex at hv
  rw [Ind.mapJoinCocone_vertex, JoinCocone.vertex_restrict] at hv
  exact hv

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
