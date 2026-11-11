module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StandardSubcomplexUpperHomotopy

/-!
# 標準ホーンと零頂点を除く面の Kan 標的の比較

概要：i ≠ 0 の標準ホーンに零頂点を除く面を含める射は Kan 標的の前合成の同値条件を満たす。
方針：両方の部分複体で最大値の変形を保ち、面を通る二つの合成と二対六則を使う。
規約：元の標準ホーンに Kan 性を仮定しない。
使われ方：HA 1.3.1.17、Kerodon Proposition 4.6.7.23（Tag 01LW） の解像側との比較の標準単体側。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：標準単体の零頂点を使わない面。
方針：零を除いた頂点集合で定まる標準の面を使う。
規約：解像側の同じ頂点集合の面に対応する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の正の欠落面のホーンの比較。 -/
def standardPositiveFace (n : ℕ) : (Δ[n] : SSet.{u}).Subcomplex :=
  SSet.stdSimplex.face (Finset.univ.erase 0)

/-- 概要：標準ホーンは指定した頂点との最大値への変形を保つ。
方針：変形の各頂点は元の頂点か i なので、i と異なる欠落頂点を保つ。
規約：全てのホーンの添字 i で成立する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の標準ホーン内への変形の制限。 -/
lemma standardHorn_upper_stable {n : ℕ} (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StandardUpperStable (SSet.horn.{u} n i) i := by
  intro d σ hσ t
  obtain ⟨j, hji, hj⟩ := (SSet.mem_horn_iff_notMem_range σ i).mp hσ
  apply (SSet.mem_horn_iff_notMem_range _ i).mpr
  refine ⟨j, hji, ?_⟩
  rintro ⟨r, hr⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardUpperVertexHomotopyMap_apply] at hr
  split at hr
  · exact hj ⟨r, hr⟩
  · by_cases h : i ≤ σ r
    · rw [max_eq_right h] at hr
      exact hj ⟨r, hr⟩
    · rw [max_eq_left (le_of_not_ge h)] at hr
      exact hji hr.symm

/-- 概要：i ≠ 0 なら零頂点を除く標準の面は最大値への変形を保つ。
方針：元の頂点は零でなく、最大値も i 以上なので零ではない。
規約：全変形中の全単体を同じ面に保つ。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の標準の面内の変形。 -/
lemma standardPositiveFace_upper_stable {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StandardUpperStable (standardPositiveFace.{u} n) i := by
  intro d σ hσ t
  apply (SSet.stdSimplex.mem_face_iff _ _).mpr
  intro r
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardUpperVertexHomotopyMap_apply]
  split
  · exact (SSet.stdSimplex.mem_face_iff _ σ).mp hσ r
  · apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro he
    have h : i ≤ max i (σ r) := le_max_left _ _
    rw [he] at h
    exact hi (le_antisymm h (Fin.zero_le i))

/-- 概要：i ≠ 0 のとき零頂点を除く標準の面はホーンに含まれる。
方針：欠落頂点の証人に零を使う。
規約：包含は同じ標準単体の部分複体間のもの。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の標準側の面からホーンへの射。 -/
lemma standardPositiveFace_le_horn {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    standardPositiveFace.{u} n ≤ SSet.horn n i := by
  intro d σ hσ
  obtain ⟨⟨d⟩⟩ := d
  apply (SSet.mem_horn_iff_notMem_range σ i).mpr
  refine ⟨0, Ne.symm hi, ?_⟩
  rintro ⟨r, hr⟩
  exact (Finset.mem_erase.mp ((SSet.stdSimplex.mem_face_iff _ σ).mp hσ r)).1 hr

/-- 概要：標準ホーンの最大値の射を零頂点を除く面へ持ち上げる。
方針：最大値は正の i 以上なので、像は零頂点を使わない。
規約：包含後の射は頂点の最大値による直接像そのもの。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の標準側の合成の因子分解。 -/
def standardHornToPositiveFace {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    (SSet.horn.{u} n i).toSSet ⟶ (standardPositiveFace n).toSSet :=
  SSet.Subcomplex.lift ((SSet.horn n i).ι ≫
      SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionUpperVertexMap i))) (by
    intro d σ hσ
    obtain ⟨⟨d⟩⟩ := d
    obtain ⟨G, rfl⟩ := hσ
    apply (SSet.stdSimplex.mem_face_iff _ _).mpr
    intro r
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro he
    change max i (G.val r) = 0 at he
    have h : i ≤ max i (G.val r) := le_max_left _ _
    rw [he] at h
    exact hi (le_antisymm h (Fin.zero_le i)))

/-- 概要：標準ホーン上の最大値の自己写像は零頂点を除く面を通る。
方針：ホーンの包含の後で二つの射を比較する。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の標準ホーン側の二対六則の入力。 -/
lemma standardHornUpperMap_factor {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    standardHornToPositiveFace.{u} i hi ≫
        SSet.Subcomplex.homOfLE (standardPositiveFace_le_horn i hi) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardSubcomplexUpperMap (SSet.horn n i) i (standardHorn_upper_stable i) := by
  apply (cancel_mono (SSet.horn n i).ι).1
  rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardSubcomplexUpperMap_ι]
  rfl

/-- 概要：標準の面からホーンに入り戻る合成は面の最大値の自己写像になる。
方針：面の包含の後で同じ標準単体の直接像へ同定する。
規約：もう一方の順序の合成の厳密な等式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の標準側の二対六則の第二の入力。 -/
lemma standardPositiveFaceUpperMap_factor {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    SSet.Subcomplex.homOfLE (standardPositiveFace_le_horn.{u} i hi) ≫
        standardHornToPositiveFace i hi =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardSubcomplexUpperMap (standardPositiveFace n) i
        (standardPositiveFace_upper_stable i hi) := by
  apply (cancel_mono (standardPositiveFace n).ι).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardSubcomplexUpperMap_ι]
  change SSet.Subcomplex.homOfLE (standardPositiveFace_le_horn i hi) ≫
    ((SSet.horn n i).ι ≫
      SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionUpperVertexMap i))) = _
  rw [← Category.assoc, SSet.Subcomplex.homOfLE_ι]

/-- 概要：正の欠落面の標準ホーンへの零頂点を除く面の包含は Kan 標的の比較を満たす。
方針：二つの合成の恒等射からの変形と二対六則を適用する。
規約：任意の Kan 標的の写像空間で実際の単体的ホモトピー逆を得る。
使われ方：HA 1.3.1.17 のホーンの解像の射影を面の射影と比較する。 -/
lemma standardPositiveFace_inclusion_isKanPrecompositionEquivalence {n : ℕ}
    (i : Fin (n + 1)) (hi : i ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsKanPrecompositionEquivalence
      (SSet.Subcomplex.homOfLE (standardPositiveFace_le_horn.{u} i hi)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isKanPrecompositionEquivalence_of_composites
    (f := standardHornToPositiveFace i hi) (h := standardHornToPositiveFace i hi)
  · rw [standardHornUpperMap_factor]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardSubcomplexUpperMap_isKanPrecompositionEquivalence _ _ _
  · rw [standardPositiveFaceUpperMap_factor]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardSubcomplexUpperMap_isKanPrecompositionEquivalence _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
