module
public import SerrePositivity.KST.SConstruction.SimplexHASplitOrder
public import SerrePositivity.KST.SConstruction.SimplexHAGeneratorValues
public import SerrePositivity.KST.SConstruction.DGForwardEquality

/-! # 元の内部切断の左右の生の HA 値の合成
概要：元の左右の生成元語を、元の切断頂点を共有する豊穣順合成として評価する。
方針：左右の列の端点を回収し、元の自由次元和を共通の出力次数に使う。
規約：右側集合内部の自由座標を保持。使われ方：任意位置の一端点挿入の値の復元。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の切断の左右の生の HA 値を、同じ切断頂点で豊穣順に合成した元。 -/
def simplexHASplitRawValue {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N)
    (n : ℕ) (i : SerreCubeGeneratorIndex n) (m : ℕ) (j : SerreCubeGeneratorIndex m)
    (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1))
    (T : Finset (Fin (N + 1))) (hT : T.Nonempty)
    (hb : ∀ r ∈ T, v (Fin.last (n + 1 + m)) < r) :
    GradedHom A (s.obj (v 0)) (s.obj (T.max' hT))
      (-((serreCubeGeneratorFreeDimension n i + serreCubeGeneratorFreeDimension m j +
        T.card - 1 : ℕ) : ℤ)) :=
  forward A
    (simplexHABeadWordRawValue A s (simplexHAGeneratorWord n i (simplexHASplitLeft n m v)
      (simplexHASplitCut n m v) (simplexHASplitLeft_last_lt n m v)))
    (simplexHABeadWordRawValue A s (simplexHABeadWordDecode m j (simplexHASplitRight n m v)
      T hT (fun r hr => lt_of_eq_of_lt (simplexHASplitRight_last n m v) (hb r hr)))) (by
        have hp := Finset.card_pos.mpr hT
        omega)

/-- 元の零次元の読み替えの生の値は、元の同じ始点と右側集合の tail 値。 -/
lemma simplexHABeadWordDecode_zero_rawTail {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N)
    (i : SerreCubeGeneratorIndex 0) (v : Fin 1 ↪o Fin (N + 1))
    (T : Finset (Fin (N + 1))) (hT : T.Nonempty) (hb : ∀ r ∈ T, v 0 < r) :
    HEq (simplexHABeadWordRawValue A s (simplexHABeadWordDecode 0 i v T hT hb))
      (simplexHABeadWordRawValue A s (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v 0) hb)) :=
  simplexHABeadWordRawValue_reindex A s rfl
    (show T.card - 1 = serreCubeGeneratorFreeDimension 0 i + T.card - 1 by
      simp only [serreCubeGeneratorFreeDimension, zero_add]) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v 0) hb)

end SerrePositivity.KST.SConstruction
