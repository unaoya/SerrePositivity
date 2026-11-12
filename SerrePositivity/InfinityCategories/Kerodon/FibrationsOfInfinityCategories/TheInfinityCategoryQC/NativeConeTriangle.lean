module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg

/-!
概要：任意の join 錐の辺上の三角形とその三つの面。
方針：点と辺の join の正規化で元の錐の二単体を取り出す。
規約：新しい三角形の充填を選択しない。
使われ方：Cat_∞ の native な錐の指定された二次の可換性。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：錐の頂点と形状の指定辺が張る標準三角形の包含。
方針：点と標準辺の join を標準二単体に正規化する。
規約：最初の頂点は錐の頂点。
使われ方：native な錐の二次の可換性の読み戻し。 -/
def coneTriangleInclusion {K : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ K) :
    (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) e
/-- 概要：錐の標準三角形の零番目の面は形状の元の辺。
方針：join の右包含を標準二単体の最後の辺と同定する。
規約：元の形状の射自体を保持する。
使われ方：三角形の底辺の関手の照合。 -/
lemma coneTriangleInclusion_zero {K : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ K) :
    stdSimplex.δ (0 : Fin 3) ≫ coneTriangleInclusion e = e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K := by
  rw [coneTriangleInclusion, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_inr]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap]
/-- 概要：錐の標準三角形の残り二面は元の辺の両端への脚。
方針：join の面写像との自然性を使う。
規約：二つの面を Fin 2 の一つの式で扱う。
使われ方：三角形の二脚の端点の照合。 -/
lemma coneTriangleInclusion_face {K : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ K) (i : Fin 2) :
    stdSimplex.δ i.succ ≫ coneTriangleInclusion e =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.δ i ≫ e) := by
  have h : stdSimplex.δ i.succ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i) := by
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).1
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_vertex_one i]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [coneTriangleInclusion, ← Category.assoc, h]
  simp only [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
/-- 概要：任意の join 錐の形状の辺上の実際の三角形。
方針：標準三角形の包含を錐の射で写す。
規約：充填の選択を追加せず元の錐の単体を取る。
使われ方：Cat_∞ の錐の二次の可換関手同型の構成。 -/
def nativeConeTriangle {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (k : K _⦋1⦌) :
    X _⦋2⦌ := SSet.yonedaEquiv (coneTriangleInclusion (SSet.yonedaEquiv.symm k) ≫ c.val)
/-- 概要：native な錐の三角形の底辺は図式が元の辺に与える像。
方針：三角形の包含の零番目の面と錐の固定条件を使う。
規約：一次単体の厳密な等式。
使われ方：底辺を元の指定関手と同定する。 -/
lemma nativeConeTriangle_zero {K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (k : K _⦋1⦌) :
    X.δ 0 (nativeConeTriangle c k) = p.app (Opposite.op ⦋1⦌) k := by
  rw [nativeConeTriangle, ← stdSimplex.yonedaEquiv_δ_comp,
    ← Category.assoc, coneTriangleInclusion_zero]
  rw [Category.assoc, c.property, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
/-- 概要：native な錐の三角形の他の二辺は元の錐の実際の脚。
方針：標準三角形の面の式と頂点の Yoneda 表示を使う。
規約：元の各脚の一単体を保持する。
使われ方：錐の三角形を二脚の関手同型として読み戻す。 -/
lemma nativeConeTriangle_face {K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (k : K _⦋1⦌) (i : Fin 2) :
    X.δ i.succ (nativeConeTriangle c k) = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c (K.δ i k)).edge := by
  rw [nativeConeTriangle, ← stdSimplex.yonedaEquiv_δ_comp,
    ← Category.assoc, coneTriangleInclusion_face]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_comp]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
