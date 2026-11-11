module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanPrecompositionEquivalence

/-!
# 正の欠落面のホーンと零頂点を除く面の Kan 標的の比較

概要：i ≠ 0 なら、零頂点を除く旗の面からホーンの旗の部分複体への包含は Kan 標的の比較を満たす。
方針：同じ一頂点の追加を面にも制限し、二つの合成をそれぞれ恒等射から変形する。
規約：ホーン全体の縮約や左 Kan 拡張との同定は別途必要。
使われ方：HA 1.3.1.17、Kerodon Proposition 4.6.7.23（Tag 01LW） の相対的な解像の位相的な比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory MonoidalCategory
open scoped _root_.Simplicial

/-- 概要：i ≠ 0 のとき一頂点の追加は零頂点を使わない旗の面を保つ。
方針：変形後の各元は元の元か i であり、どちらも零でないことを使う。
規約：単位区間の任意の単体で成り立つ。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の面上の変形の制限。 -/
lemma resolutionInsertVertex_mem_positiveFace {n d : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (t : Fin (d + 1) →o Fin 2)
    (hF : ULift.up F ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace.{u} n).obj (Opposite.op ⦋d⦌)) :
    ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex F i t) ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace.{u} n).obj (Opposite.op ⦋d⦌) := by
  intro k hk
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex_no_new_vertices F i t (Fin.last d) hk with rfl | hk
  · exact Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩
  · exact hF hk

/-- 概要：頂点との最大値の自己写像を零頂点を使わない旗の面へ制限する。
方針：一頂点の追加の一端点での面の保存を使う。
規約：包含後の作用は元の直接像と同じ。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の二つ目の合成の記述。 -/
def resolutionPositiveFaceUpperMap {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace.{u} n).toSSet ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace n).toSSet :=
  SSet.Subcomplex.lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace n).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionUpperVertexMap i)) (by
    intro d F hF
    obtain ⟨G, rfl⟩ := hF
    change ULift.up (G.val.down.pushforward (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionUpperVertexMap i)) ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace.{u} n).obj d
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex_one G.val.down i]
    exact resolutionInsertVertex_mem_positiveFace.{u} i hi G.val.down
      (OrderHom.const _ 1) G.property)

/-- 概要：面上の最大値の自己写像は全体の自己写像と包含を通じて整合する。
方針：部分複体への持ち上げの可換式を使う。
規約：単体集合の射の等式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の合成の因子分解の検査。 -/
lemma resolutionPositiveFaceUpperMap_ι {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    resolutionPositiveFaceUpperMap.{u} i hi ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace n).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace n).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionUpperVertexMap i) := rfl

/-- 概要：一頂点の追加の変形を零頂点を使わない旗の面へ制限する。
方針：全変形中の台の条件の保存で射を持ち上げる。
規約：元の変形の各単体の値を保つ。
使われ方：HA 1.3.1.17 の面上の実際のホモトピーの台。 -/
def resolutionPositiveFaceInsertHomotopyMap {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace.{u} n).toSSet ⊗ Δ[1] ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace n).toSSet :=
  SSet.Subcomplex.lift (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace n).ι ▷ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertHomotopyMap i) (by
    intro d F hF
    obtain ⟨G, rfl⟩ := hF
    exact resolutionInsertVertex_mem_positiveFace.{u} i hi G.1.val.down
      G.2.down.toOrderHom G.1.property)

/-- 概要：面の恒等射は選んだ正の頂点との最大値の自己写像とホモトピックである。
方針：制限した変形の両端を元の旗の端点の式で計算する。
規約：ホモトピー全体が零頂点を使わない同じ面に入る。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） のホーンと面の二つの合成の比較。 -/
def resolutionPositiveFaceInsertHomotopy {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    SSet.Homotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace.{u} n).toSSet)
      (resolutionPositiveFaceUpperMap i hi) where
  h := resolutionPositiveFaceInsertHomotopyMap i hi
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

/-- 概要：面からホーンに入り最大値で面へ戻る合成は面の最大値の自己写像になる。
方針：面への包含を後合成して、全体の解像への同じ直接像を比較する。
規約：既存のホーン上の逆順の因子分解と合わせて使う。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の二対六則のもう一方の合成。 -/
lemma resolutionPositiveFaceUpperMap_factor {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    SSet.Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace_le_horn.{u} i hi) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHornToPositiveFace i hi = resolutionPositiveFaceUpperMap i hi := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace n).ι).1
  rw [Category.assoc, resolutionPositiveFaceUpperMap_ι]
  change SSet.Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace_le_horn i hi) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHorn i).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionUpperVertexMap i)) = _
  rw [← Category.assoc, SSet.Subcomplex.homOfLE_ι]

/-- 概要：面上の最大値の自己写像は Kan 標的の前合成の同値条件を満たす。
方針：同じ面内の恒等射からのホモトピーを使う。
規約：面自身の Kan 性は仮定しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の面とホーンの比較の二つ目の入力。 -/
lemma resolutionPositiveFaceUpperMap_isKanPrecompositionEquivalence {n : ℕ}
    (i : Fin (n + 1)) (hi : i ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsKanPrecompositionEquivalence (resolutionPositiveFaceUpperMap.{u} i hi) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isKanPrecompositionEquivalence_iff_of_homotopy
    (resolutionPositiveFaceInsertHomotopy i hi)).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isKanPrecompositionEquivalence_id _)

/-- 概要：正の欠落面のホーンには零頂点を使わない旗の面から Kan 標的の比較が成り立つ。
方針：二つの合成がそれぞれ恒等射から変形されることと二対六則を使う。
規約：任意の Kan 標的への内部 Hom で実際の単体的ホモトピー逆が存在するという主張。
使われ方：HA 1.3.1.17、ホーンの解像の比較を面の比較へ接続する位相的な部分。 -/
lemma resolutionPositiveFace_inclusion_isKanPrecompositionEquivalence {n : ℕ}
    (i : Fin (n + 1)) (hi : i ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsKanPrecompositionEquivalence
      (SSet.Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace_le_horn.{u} i hi)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isKanPrecompositionEquivalence_of_composites
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHornToPositiveFace i hi) (h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHornToPositiveFace i hi)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHornUpperMap_factor_positiveFace]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHornUpperMap_isKanPrecompositionEquivalence i
  · rw [resolutionPositiveFaceUpperMap_factor]
    exact resolutionPositiveFaceUpperMap_isKanPrecompositionEquivalence i hi

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
