module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionInsertHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionSupport

/-!
# ホーンの解像上の一頂点の追加によるホモトピー

概要：選んだホーンの欠落面の頂点だけを追加する変形は、ホーンに対応する旗の部分複体を保つ。
方針：別の欠落頂点を証人として保持し、全体の変形を部分複体へ制限する。
規約：ここでのホーンの解像は台の条件で与える模型。左 Kan 拡張との同定は別途必要。
使われ方：HA 1.3.1.17、Kerodon Proposition 4.6.7.23（Tag 01LW） の相対的な比較の組み合わせ論。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory MonoidalCategory
open scoped _root_.Simplicial

/-- 概要：指定した頂点以外の少なくとも一頂点を使わない旗の部分複体。
方針：引き戻しで台が増えないことにより欠落頂点を保つ。
規約：Λ[n,i] に対応する旗の模型で、全体の境界とは区別する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） のホーンに対する解像の縮約。 -/
def resolutionHorn {n : ℕ} (i : Fin (n + 1)) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n).Subcomplex where
  obj _ := {F | ∃ j : Fin (n + 1), j ≠ i ∧ j ∉ F.down.support}
  map {a b} α F hF := by
    obtain ⟨j, hji, hj⟩ := hF
    exact ⟨j, hji, fun h ↦ hj (F.down.support_pullback_subset α.unop.toOrderHom h)⟩

/-- 概要：ホーンに属する旗に指定した頂点だけを追加しても同じホーンに属する。
方針：元の欠落頂点は追加する頂点と異なるので追加されない。
規約：単位区間の全ての単体で成り立つ。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の変形の部分複体への制限。 -/
lemma resolutionInsertVertex_mem_horn {n d : ℕ} (i : Fin (n + 1))
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (t : Fin (d + 1) →o Fin 2)
    (hF : ULift.up F ∈ (resolutionHorn.{u} i).obj (Opposite.op ⦋d⦌)) :
    ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex F i t) ∈ (resolutionHorn.{u} i).obj (Opposite.op ⦋d⦌) := by
  obtain ⟨j, hji, hj⟩ := hF
  refine ⟨j, hji, fun h ↦ ?_⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex_no_new_vertices F i t (Fin.last d) h).elim hji hj

/-- 概要：選んだ頂点との最大値の直接像はホーンの旗の部分複体を保つ。
方針：一頂点の追加の変形の一端点として計算する。
規約：任意の旗の次数での所属を述べる。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の制限した変形の終端。 -/
lemma resolutionUpperVertex_mem_horn {n d : ℕ} (i : Fin (n + 1))
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (hF : ULift.up F ∈ (resolutionHorn.{u} i).obj (Opposite.op ⦋d⦌)) :
    ULift.up (F.pushforward (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionUpperVertexMap i)) ∈
      (resolutionHorn.{u} i).obj (Opposite.op ⦋d⦌) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex_one F i]
  exact resolutionInsertVertex_mem_horn.{u} i F (OrderHom.const _ 1) hF

/-- 概要：頂点との最大値による解像の自己写像をホーンの部分複体へ制限する。
方針：台の欠落条件の保存により部分複体へ持ち上げる。
規約：制限前と同じ単体上の作用を持つ。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の相対的な変形の終端の射。 -/
def resolutionHornUpperMap {n : ℕ} (i : Fin (n + 1)) :
    (resolutionHorn.{u} i).toSSet ⟶ (resolutionHorn i).toSSet :=
  SSet.Subcomplex.lift ((resolutionHorn i).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionUpperVertexMap i))
    (by
      intro d F hF
      obtain ⟨G, rfl⟩ := hF
      exact resolutionUpperVertex_mem_horn.{u} i G.val.down G.property)

/-- 概要：ホーン上の頂点の最大値の射は包含後に全体の射と一致する。
方針：部分複体への持ち上げの可換式を使う。
規約：単体集合の射の等式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の全体の解像との整合。 -/
lemma resolutionHornUpperMap_ι {n : ℕ} (i : Fin (n + 1)) :
    resolutionHornUpperMap.{u} i ≫ (resolutionHorn i).ι =
      (resolutionHorn i).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionUpperVertexMap i) := rfl

/-- 概要：一頂点の追加の変形をホーンと単位区間の積からの射に制限する。
方針：変形が同じ欠落頂点を保つことにより全体の射を持ち上げる。
規約：全体の変形の値をそのまま用いる。
使われ方：HA 1.3.1.17 のホーンの解像の位相的な比較の準備。 -/
def resolutionHornInsertHomotopyMap {n : ℕ} (i : Fin (n + 1)) :
    (resolutionHorn.{u} i).toSSet ⊗ Δ[1] ⟶ (resolutionHorn i).toSSet :=
  SSet.Subcomplex.lift (((resolutionHorn i).ι ▷ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertHomotopyMap i) (by
    intro d F hF
    obtain ⟨G, rfl⟩ := hF
    exact resolutionInsertVertex_mem_horn.{u} i G.1.val.down G.2.down.toOrderHom G.1.property)

/-- 概要：ホーン上の変形は包含後に全体の変形と一致する。
方針：部分複体への持ち上げの定義を評価する。
規約：単位区間を含む実際の射の可換式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の相対的な変形の検査。 -/
lemma resolutionHornInsertHomotopyMap_ι {n : ℕ} (i : Fin (n + 1)) :
    resolutionHornInsertHomotopyMap.{u} i ≫ (resolutionHorn i).ι =
      ((resolutionHorn i).ι ▷ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertHomotopyMap i := rfl

/-- 概要：ホーンの旗の部分複体の恒等射は頂点との最大値の制限とホモトピックである。
方針：制限した変形の両端を旗の端点の計算で確かめる。
規約：全体の解像での一致だけでなく同じホーン内のホモトピーを与える。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） のホーンの解像の縮約の第一段階。 -/
def resolutionHornInsertHomotopy {n : ℕ} (i : Fin (n + 1)) :
    SSet.Homotopy (𝟙 (resolutionHorn.{u} i).toSSet) (resolutionHornUpperMap i) where
  h := resolutionHornInsertHomotopyMap i
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    apply ULift.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex_zero F.val.down i
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    apply ULift.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex_one F.val.down i
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.2

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
