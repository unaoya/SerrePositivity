module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinSimplexInclusions
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-! # span と標準単体の join の二セル

概要：coslice の単体の形状 Λ[2,0]⋆Δ[n] を二つの標準単体の pushout として表示する。
方針：右因子を固定した join 関手で span の pushout を送り、標準 join 同型で移す。
規約：二セルは A,B と A,C を先頭に持ち、共通面では二番目の頂点を除く。
使われ方：D7 の cofiber 余錐の coslice の境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits
open scoped _root_.Simplicial

/-- 概要：標準 join 同型の次元を指定した自然数へ正規化する。
方針：標準単体の次元の等式による同型を後合成する。
規約：頂点の自然数値は保つ。使われ方：coslice の可変次元のセルの統一。 -/
def cofiberJoinStdSimplexIso (p q r : ℕ) (h : p + q + 1 = r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[p] : SSet.{u}) Δ[q] ≅ Δ[r] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso p q ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.simplexCastIso h

/-- 概要：正規化後の左の頂点包含は添字を保つ。
方針：左区間の自然数値をそのまま用いる。
規約：r=p+q+1。使われ方：標準 join の左包含の照合。 -/
def cofiberJoinLeftOrderHom (p q r : ℕ) (h : p + q + 1 = r) : Fin (p + 1) →o Fin (r + 1) where
  toFun i := ⟨i.val, by have := i.isLt; omega⟩
  monotone' _ _ hi := hi

/-- 概要：正規化後の右の頂点包含は p+1 だけ移す。
方針：右区間の値に左の頂点数を加える。
規約：r=p+q+1。使われ方：標準 join の右包含の照合。 -/
def cofiberJoinRightOrderHom (p q r : ℕ) (h : p + q + 1 = r) : Fin (q + 1) →o Fin (r + 1) where
  toFun i := ⟨p + 1 + i.val, by have := i.isLt; omega⟩
  monotone' _ _ hi := Nat.add_le_add_left hi _

/-- 概要：正規化した標準 join 同型の左包含の式。
方針：元の包含の式と次元輸送の値の保存を使う。
規約：標準単体の射としての厳密な等式。使われ方：共通面の左区間の計算。 -/
lemma cofiberJoinStdSimplexIso_inl (p q r : ℕ) (h : p + q + 1 = r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[p] : SSet.{u}) Δ[q] ≫ (cofiberJoinStdSimplexIso p q r h).hom =
      SSet.stdSimplex.map (SimplexCategory.mkHom (cofiberJoinLeftOrderHom p q r h)) := by
  rw [cofiberJoinStdSimplexIso, Iso.trans_hom, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl]
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  rw [SSet.yonedaEquiv_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.simplexCastIso_hom_app_val h p _ i

/-- 概要：正規化した標準 join 同型の右包含の式。
方針：元の包含の式と次元輸送の値の保存を使う。
規約：標準単体の射としての厳密な等式。使われ方：共通面の右区間の計算。 -/
lemma cofiberJoinStdSimplexIso_inr (p q r : ℕ) (h : p + q + 1 = r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[p] : SSet.{u}) Δ[q] ≫ (cofiberJoinStdSimplexIso p q r h).hom =
      SSet.stdSimplex.map (SimplexCategory.mkHom (cofiberJoinRightOrderHom p q r h)) := by
  rw [cofiberJoinStdSimplexIso, Iso.trans_hom, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inr]
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  rw [SSet.yonedaEquiv_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.simplexCastIso_hom_app_val h q _ i

/-- 概要：span の二セルの共通面で取り除く第二頂点。
方針：値が一の有限添字を使う。
規約：先頭の A は保つ。使われ方：共通面の写像。 -/
def spanJoinCommonFace (n : ℕ) : Fin (n + 3) := ⟨1, by omega⟩

/-- 概要：span の第一辺と標準単体との join のセル。
方針：標準 join 同型の逆と第一辺の包含を合成する。
規約：先頭の二頂点は A,B。使われ方：coslice の左セル。 -/
def spanJoinLeft (n : ℕ) : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0) Δ[n] :=
  (cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap SSet.horn₂₀.ι₀₁ (𝟙 Δ[n])

/-- 概要：span の第二辺と標準単体との join のセル。
方針：標準 join 同型の逆と第二辺の包含を合成する。
規約：先頭の二頂点は A,C。使われ方：coslice の右セル。 -/
def spanJoinRight (n : ℕ) : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0) Δ[n] :=
  (cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap SSet.horn₂₀.ι₀₂ (𝟙 Δ[n])

/-- 概要：左因子の始点との join は第二頂点を除いた面になる。
方針：左右の包含で比較し、右の頂点の添字が一つ後ろへずれることを計算する。
規約：左因子の面は δ₁。使われ方：二セルの共通面の標準表示。 -/
lemma cofiberJoinStdSimplexIso_left_first (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ (1 : Fin 2)) (𝟙 (Δ[n] : SSet.{u})) ≫
        (cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).hom =
      (cofiberJoinStdSimplexIso 0 n (n + 1) (by omega)).hom ≫
        SSet.stdSimplex.δ (spanJoinCommonFace n) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_hom_to_stdSimplex_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc,
      cofiberJoinStdSimplexIso_inl, ← Category.assoc, cofiberJoinStdSimplexIso_inl]
    change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ SSet.stdSimplex.map _ =
      SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map (SimplexCategory.δ (spanJoinCommonFace n))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    apply congrArg SSet.stdSimplex.map
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    fin_cases i
    rfl
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp,
      cofiberJoinStdSimplexIso_inr, ← Category.assoc, cofiberJoinStdSimplexIso_inr]
    change SSet.stdSimplex.map _ = SSet.stdSimplex.map _ ≫
      SSet.stdSimplex.map (SimplexCategory.δ (spanJoinCommonFace n))
    rw [← CategoryTheory.Functor.map_comp]
    apply congrArg SSet.stdSimplex.map
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    change cofiberJoinRightOrderHom 1 n (n + 2) (by omega) i =
      (spanJoinCommonFace n).succAbove (cofiberJoinRightOrderHom 0 n (n + 1) (by omega) i)
    rw [Fin.succAbove_of_le_castSucc _ _ (by change 1 ≤ 0 + 1 + i.val; omega)]
    apply Fin.ext
    change 1 + 1 + i.val = (0 + 1 + i.val) + 1
    omega

/-- 概要：span と標準単体の join は二つの標準セルを共通面で貼る pushout。
方針：span の pushout の join と標準単体の同型で普遍性を移す。
規約：共通面は第二頂点を除く面。使われ方：二つの充填済み dg nerve 単体の貼合せ。 -/
lemma spanJoin_isPushout (n : ℕ) :
    IsPushout (SSet.stdSimplex.δ (spanJoinCommonFace n))
      (SSet.stdSimplex.δ (spanJoinCommonFace n)) (spanJoinLeft.{u} n) (spanJoinRight n) := by
  apply (SSet.horn₂₀.isPushout.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftFunctor (Δ[n] : SSet.{u}))).of_iso'
    (cofiberJoinStdSimplexIso 0 n (n + 1) (by omega)).symm
    (cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).symm
    (cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).symm (Iso.refl _)
  · apply (cancel_mono (cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).hom).1
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change (cofiberJoinStdSimplexIso 0 n (n + 1) (by omega)).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ (1 : Fin 2)) (𝟙 (Δ[n] : SSet.{u})) ≫
      (cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).hom = _
    rw [cofiberJoinStdSimplexIso_left_first, Iso.inv_hom_id_assoc]
  · apply (cancel_mono (cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).hom).1
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change (cofiberJoinStdSimplexIso 0 n (n + 1) (by omega)).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ (1 : Fin 2)) (𝟙 (Δ[n] : SSet.{u})) ≫
      (cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).hom = _
    rw [cofiberJoinStdSimplexIso_left_first, Iso.inv_hom_id_assoc]
  · rfl
  · rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
