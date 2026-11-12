module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWFaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IntegerTensorAdditivity

/-!
# AW の制限項と全複体の二つの微分

概要：AW の各斉次制限項に全複体の水平・垂直微分を適用し、面の和へ展開する。
方針：全複体の標準包含の微分公式とテンソル写像の双加法性を使う。
規約：KST Construction A.5 の標準 AW、垂直微分の符号は第一因子の次数。
使われ方：左右の非対角項の添字変換と切断点の対角項の相殺。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology
open scoped Simplicial
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 概要：二つの単体的制限から全テンソルの斉次成分への写像を作る。
方針：二つの制限のテンソルを全次数の標準包含へ送る。
規約：KST A.5 の AW、制限を共有切断点の形に限定しない。
使われ方：面を削除した後の AW の項の共通表示。 -/
def awTensorTerm {N p q n : ℕ} (f : ⦋p⦌ ⟶ ⦋N⦌) (g : ⦋q⦌ ⟶ ⦋N⦌) (h : p + q = n) :
    (simplicialIntegerTensor C D).obj (op ⦋N⦌) ⟶
      (chainIntegerTensor ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D)).X n :=
  integerTensorMap (C.map f.op) (D.map g.op) ≫
    ιMapBifunctor ((alternatingFaceMapComplex _).obj C)
      ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) p q n h

/-- 概要：AW の斉次制限項の水平微分は第一因子の面の交代和。
方針：標準包含の水平微分を使い、整数テンソル写像の第一変数で和を展開する。
規約：KST A.5 の標準 AW、第一因子の次数は p+1。
使われ方：前半の境界を削除後の切断へ移す。 -/
lemma awTensorTerm_D₁ {N p q n : ℕ} (f : ⦋p + 1⦌ ⟶ ⦋N⦌) (g : ⦋q⦌ ⟶ ⦋N⦌) (h : p + q = n) :
    awTensorTerm C D f g (by omega) ≫
      mapBifunctor.D₁ ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ)
        (n + 1) n =
      ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
        awTensorTerm C D (SimplexCategory.δ k ≫ f) g h := by
  rw [awTensorTerm, Category.assoc, mapBifunctor.ι_D₁,
    mapBifunctor.d₁_eq _ _ _ _ (i₁ := p + 1) (i₁' := p) rfl q n h]
  have hε : ComplexShape.ε₁ (.down ℕ) (.down ℕ) (.down ℕ) (p + 1, q) = 1 := rfl
  rw [hε, one_smul]
  change integerTensorMap (C.map f.op) (D.map g.op) ≫
    (integerTensorMap (((alternatingFaceMapComplex _).obj C).d (p + 1) p) (𝟙 _) ≫ _) = _
  rw [← Category.assoc, ← integerTensorMap_comp, Category.comp_id,
    alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD,
    Preadditive.comp_sum, integerTensorMap_sum_left, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [Preadditive.comp_zsmul, integerTensorMap_zsmul_left, Preadditive.zsmul_comp]
  congr 1
  simp only [awTensorTerm, op_comp, C.map_comp, SimplicialObject.δ]

/-- 概要：AW の斉次制限項の垂直微分は第二因子の面の符号付き交代和。
方針：標準包含の垂直微分を展開し、第一因子の次数の符号を保持する。
規約：KST A.5 の標準 AW、全複体の Koszul 符号は (−1)^p。
使われ方：後半の境界を削除後の切断へ移す。 -/
lemma awTensorTerm_D₂ {N p q n : ℕ} (f : ⦋p⦌ ⟶ ⦋N⦌) (g : ⦋q + 1⦌ ⟶ ⦋N⦌) (h : p + q = n) :
    awTensorTerm C D f g (by omega) ≫
      mapBifunctor.D₂ ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ)
        (n + 1) n =
      (-1 : ℤ) ^ p • (∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
        awTensorTerm C D f (SimplexCategory.δ k ≫ g) h) := by
  rw [awTensorTerm, Category.assoc, mapBifunctor.ι_D₂,
    mapBifunctor.d₂_eq _ _ _ _ p (i₂ := q + 1) (i₂' := q) rfl n h]
  have hε : ComplexShape.ε₂ (.down ℕ) (.down ℕ) (.down ℕ) (p, q + 1) =
      (-1 : ℤˣ) ^ p := rfl
  rw [hε, Units.smul_def]
  change integerTensorMap (C.map f.op) (D.map g.op) ≫
    ((-1 : ℤ) ^ p • (integerTensorMap (𝟙 _)
      (((alternatingFaceMapComplex _).obj D).d (q + 1) q) ≫ _)) = _
  rw [Preadditive.comp_zsmul]
  congr 1
  rw [← Category.assoc, ← integerTensorMap_comp, Category.comp_id,
    alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD,
    Preadditive.comp_sum, integerTensorMap_sum_right, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [Preadditive.comp_zsmul, integerTensorMap_zsmul_right, Preadditive.zsmul_comp]
  congr 1
  simp only [awTensorTerm, op_comp, D.map_comp, SimplicialObject.δ]

/-- 概要：零次の第一因子を持つ制限項の水平微分は零。
方針：零次の鎖複体には出ていく水平微分がないことを使う。
規約：KST A.5、非被約複体の零次を含む。
使われ方：境界和の最初の切断点。 -/
lemma awTensorTerm_zero_D₁ {N q n s : ℕ} (f : ⦋0⦌ ⟶ ⦋N⦌) (g : ⦋q⦌ ⟶ ⦋N⦌)
    (h : 0 + q = s) :
    awTensorTerm C D f g h ≫
      mapBifunctor.D₁ ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) s n = 0 := by
  rw [awTensorTerm, Category.assoc, mapBifunctor.ι_D₁,
    mapBifunctor.d₁_eq_zero _ _ _ _ 0 q n (by simp), Limits.comp_zero]

/-- 概要：零次の第二因子を持つ制限項の垂直微分は零。
方針：零次の鎖複体には出ていく垂直微分がないことを使う。
規約：KST A.5、非被約複体の零次を含む。
使われ方：境界和の最後の切断点。 -/
lemma awTensorTerm_zero_D₂ {N p n s : ℕ} (f : ⦋p⦌ ⟶ ⦋N⦌) (g : ⦋0⦌ ⟶ ⦋N⦌)
    (h : p + 0 = s) :
    awTensorTerm C D f g h ≫
      mapBifunctor.D₂ ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) s n = 0 := by
  rw [awTensorTerm, Category.assoc, mapBifunctor.ι_D₂,
    mapBifunctor.d₂_eq_zero _ _ _ _ p 0 n (by simp), Limits.comp_zero]

/-- 概要：全単体の面を先に取ることは、二つの制限に面を後合成することに等しい。
方針：テンソル写像の合成則と二つの反変関手の合成則を使う。
規約：KST A.5 の標準 AW。使われ方：source の境界と削除後の切断の同定。 -/
lemma awTensorTerm_source_face {N p q n : ℕ} (k : Fin (N + 2))
    (f : ⦋p⦌ ⟶ ⦋N⦌) (g : ⦋q⦌ ⟶ ⦋N⦌) (h : p + q = n) :
    integerTensorMap (C.δ k) (D.δ k) ≫ awTensorTerm C D f g h =
      awTensorTerm C D (f ≫ SimplexCategory.δ k) (g ≫ SimplexCategory.δ k) h := by
  dsimp only [awTensorTerm]
  rw [← Category.assoc, ← integerTensorMap_comp]
  simp only [op_comp, C.map_comp, D.map_comp, SimplicialObject.δ]

/-- 概要：区間の最後の頂点を削除すると長さだけ一つ減る。
方針：残った頂点は全て削除点より前にある。
規約：KST A.5 の AW。使われ方：水平境界の対角項。 -/
lemma awInterval_face_last (a l n : ℕ) (h : a + (l + 1) ≤ n) :
    SimplexCategory.δ (Fin.last (l + 1)) ≫ awInterval a (l + 1) n h =
      awInterval a l n (by omega) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    awInterval_apply, awFace_apply, Fin.val_last]
  have hj : (j : ℕ) < l + 1 := j.isLt
  split_ifs <;> omega

/-- 概要：区間の最初の頂点を削除すると開始点が一つ増える。
方針：零番目を飛ばす面は全ての頂点番号を一つ増やす。
規約：KST A.5 の AW。使われ方：垂直境界の対角項。 -/
lemma awInterval_face_zero (a l n : ℕ) (h : a + (l + 1) ≤ n) :
    SimplexCategory.δ (0 : Fin (l + 2)) ≫ awInterval a (l + 1) n h =
      awInterval (a + 1) l n (by omega) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    awInterval_apply, awFace_apply, Fin.val_zero, not_lt_zero, ite_false]
  omega

/-- 概要：切断点に由来する水平境界項と垂直境界項の符号は逆で相殺する。
方針：(−1) の連続する冪の和を計算する。
規約：KST A.5、全複体の垂直微分の符号を含む。
使われ方：AW の鎖写像性の対角項の相殺。 -/
lemma awDiagonal_sign_cancel {A : Type*} [AddCommGroup A] (p : ℕ) (x : A) :
    (-1 : ℤ) ^ (p + 1) • x + (-1 : ℤ) ^ p • x = 0 := by
  simp [pow_succ]

/-- 概要：source の交代境界の後に AW を取ると、削除点と切断点の二重和になる。
方針：交代境界と AW の有限和を展開し、制限への面の後合成に置き換える。
規約：KST Construction A.5 の標準 AW、符号は削除点の番号。
使われ方：target の水平・垂直境界和との比較。 -/
lemma alexanderWhitney_source_boundary (n : ℕ) :
    ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (n + 1) n ≫
      alexanderWhitneyApp C D n =
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
      (∑ i : Fin (n + 1), awTensorTerm C D
        (awFront n i ≫ SimplexCategory.δ k) (awBack n i ≫ SimplexCategory.δ k) (awDegrees n i)) := by
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, alexanderWhitneyApp,
    Preadditive.comp_sum]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact awTensorTerm_source_face C D k (awFront n i) (awBack n i) (awDegrees n i)

/-- 概要：後半の区間の長さの等式に沿って斉次制限項を同定する。
方針：長さの等式を代入し、境界や包含の証明引数の差を除く。
規約：KST A.5、全次数と始域は固定。
使われ方：n+1−i=(n−i)+1 による垂直微分の次数の整理。 -/
lemma awTensorTerm_interval_congr {N p n a q q' : ℕ} (f : ⦋p⦌ ⟶ ⦋N⦌)
    (hq : q = q') (h : a + q ≤ N) (h' : a + q' ≤ N)
    (hn : p + q = n) (hn' : p + q' = n) :
    awTensorTerm C D f (awInterval a q N h) hn =
      awTensorTerm C D f (awInterval a q' N h') hn' := by
  subst q'
  rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories




