module

public import SerrePositivity.KST.Descent.SplitCech
public import SerrePositivity.KST.Descent.CechHomotopyIndex

/-!
# 同じ基底上の Čech 細分比較のホモトピー

## 概要
同じ基底上の二つの持ち上げからの Čech 比較の間に、実際の単体ホモトピーを構成する。

## 方針
重複する座標と二つの比較射を切り替えるタグを使い、全恒等式を二射影で検査する。

## 規約
射の点ごとの一致は要求しない。通常の極限で Tot を代用しない。

## 使われ方
論文 補題 3.2 の τ 位相の層論を Čech 計算で置換する細分比較。
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] {X W Y : C}
  (f : X ⟶ Y) (g : W ⟶ Y) (a b : X ⟶ W)
  (ha : a ≫ g = f) (hb : b ≫ g = f)

/-- 概要：指定された基底上の持ち上げからの Čech 比較（論文 補題 3.2）。
方針：基底側を恒等射とした Arrow の射に Čech nerve を適用する。
規約：指定された持ち上げそのものを使う。
使われ方：細分ホモトピーの両端。 -/
noncomputable def refinementCechMap : (Arrow.mk f).cechNerve ⟶ (Arrow.mk g).cechNerve :=
  Arrow.mapCechNerve (Arrow.homMk a (𝟙 Y) (ha.trans (Category.comp_id f).symm))

omit g b ha hb in
/-- 概要：面射と Čech の指定座標の合成（論文 補題 3.2）。
方針：wide pullback の lift の指定射影の公式を使う。
規約：除かれる座標は succAbove で指定する。
使われ方：細分ホモトピーの面射の恒等式。 -/
@[reassoc] theorem cechFace_π {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (Arrow.mk f).cechNerve.δ i ≫ WidePullback.π (fun _ : Fin (n + 1) ↦ f) j =
      WidePullback.π (fun _ : Fin (n + 2) ↦ f) (i.succAbove j) :=
  WidePullback.lift_π _ _ _ _ _

omit g b ha hb in
/-- 概要：退化射と Čech の指定座標の合成（論文 補題 3.2）。
方針：wide pullback の lift の指定射影の公式を使う。
規約：重複する座標は predAbove で指定する。
使われ方：細分ホモトピーの退化射の恒等式。 -/
@[reassoc] theorem cechDegeneracy_π {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (Arrow.mk f).cechNerve.σ i ≫ WidePullback.π (fun _ : Fin (n + 2) ↦ f) j =
      WidePullback.π (fun _ : Fin (n + 1) ↦ f) (i.predAbove j) :=
  WidePullback.lift_π _ _ _ _ _

/-- 概要：細分比較の各指定座標（論文 補題 3.2）。
方針：Arrow の比較の lift の合成公式を使う。
規約：始域の指定座標に a を合成する。
使われ方：細分ホモトピーの両端の検査。 -/
@[reassoc] theorem refinementCechMap_π (n : ℕ) (j : Fin (n + 1)) :
    (refinementCechMap f g a ha).app (op ⦋n⦌) ≫
        WidePullback.π (fun _ : Fin (n + 1) ↦ g) j =
      WidePullback.π (fun _ : Fin (n + 1) ↦ f) j ≫ a :=
  WidePullback.lift_π _ _ _ _ _

/-- 概要：細分ホモトピーの指定座標に二つの比較射を適用（論文 補題 3.2）。
方針：タグ 0 なら a、それ以外なら b を指定座標に合成する。
規約：タグは有限添字の計算から供給する。
使われ方：ホモトピーの wide pullback の成分。 -/
noncomputable def refinementCechCoordinate (n : ℕ) (c : Fin (n + 1) × ℕ) :
    (Arrow.mk f).cechNerve.obj (op ⦋n⦌) ⟶ W :=
  WidePullback.π (fun _ : Fin (n + 1) ↦ f) c.1 ≫ (if c.2 = 0 then a else b)

include ha hb in
/-- 概要：切替座標の射は共通の基底上にある（論文 補題 3.2）。
方針：二つの比較射が基底上にあることを使う。
規約：全てのタグを扱う。
使われ方：ホモトピーの各射を引き戻しへ持ち上げる。 -/
theorem refinementCechCoordinate_over_base (n : ℕ) (c : Fin (n + 1) × ℕ) :
    refinementCechCoordinate f a b n c ≫ g =
      WidePullback.base (fun _ : Fin (n + 1) ↦ f) := by
  dsimp only [refinementCechCoordinate]
  split_ifs <;> simp only [Category.assoc, ha, hb, WidePullback.π_arrow]

/-- 概要：細分ホモトピーの次数ごとの実際の射（論文 補題 3.2）。
方針：切替添字の各座標を共通基底の wide pullback へ持ち上げる。
規約：面射・退化射の恒等式は後続で検査する。
使われ方：二つの Čech 比較の間のホモトピー。 -/
noncomputable def refinementCechHomotopyMap {n : ℕ} (i : Fin (n + 1)) :
    (Arrow.mk f).cechNerve.obj (op ⦋n⦌) ⟶ (Arrow.mk g).cechNerve.obj (op ⦋n + 1⦌) :=
  WidePullback.lift (WidePullback.base _) (fun j ↦
    refinementCechCoordinate f a b n (cechMixIndex i j))
    (fun j ↦ refinementCechCoordinate_over_base f g a b ha hb n (cechMixIndex i j))

/-- 概要：細分ホモトピーの指定座標の評価（論文 補題 3.2）。
方針：実際の wide pullback の lift の公式を使う。
規約：座標と比較射のタグを保持する。
使われ方：全ホモトピー恒等式の二射影での検査。 -/
@[reassoc] theorem refinementCechHomotopyMap_π {n : ℕ} (i : Fin (n + 1))
    (j : Fin (n + 2)) :
    refinementCechHomotopyMap f g a b ha hb i ≫
        WidePullback.π (fun _ : Fin (n + 2) ↦ g) j =
      refinementCechCoordinate f a b n (cechMixIndex i j) :=
  WidePullback.lift_π _ _ _ _ _

omit g ha hb in
/-- 概要：面射は切替座標の元の添字に作用する（論文 補題 3.2）。
方針：タグを固定し、元の Čech の面射の座標公式を使う。
規約：比較射のタグを変更しない。
使われ方：ホモトピーの面射の恒等式。 -/
@[reassoc] theorem cechFace_coordinate {n : ℕ} (i : Fin (n + 2))
    (c : Fin (n + 1) × ℕ) :
    (Arrow.mk f).cechNerve.δ i ≫ refinementCechCoordinate f a b n c =
      refinementCechCoordinate f a b (n + 1) (i.succAbove c.1, c.2) := by
  dsimp only [refinementCechCoordinate]
  split_ifs <;> simp only [cechFace_π_assoc]

omit g ha hb in
/-- 概要：退化射は切替座標の元の添字に作用する（論文 補題 3.2）。
方針：タグを固定し、元の Čech の退化射の座標公式を使う。
規約：比較射のタグを変更しない。
使われ方：ホモトピーの退化射の恒等式。 -/
@[reassoc] theorem cechDegeneracy_coordinate {n : ℕ} (i : Fin (n + 1))
    (c : Fin (n + 2) × ℕ) :
    (Arrow.mk f).cechNerve.σ i ≫ refinementCechCoordinate f a b (n + 1) c =
      refinementCechCoordinate f a b n (i.predAbove c.1, c.2) := by
  dsimp only [refinementCechCoordinate]
  split_ifs <;> simp only [cechDegeneracy_π_assoc]

omit g a b ha hb in
/-- 概要：Čech の面射は増強を保つ（論文 補題 3.2）。
方針：wide pullback の lift の基底への公式を使う。
規約：指定増強の等式。
使われ方：ホモトピーの基底側の恒等式。 -/
@[reassoc] theorem cechFace_base {n : ℕ} (i : Fin (n + 2)) :
    (Arrow.mk f).cechNerve.δ i ≫ WidePullback.base (fun _ : Fin (n + 1) ↦ f) =
      WidePullback.base (fun _ : Fin (n + 2) ↦ f) :=
  WidePullback.lift_base _ _ _ _

omit g a b ha hb in
/-- 概要：Čech の退化射は増強を保つ（論文 補題 3.2）。
方針：wide pullback の lift の基底への公式を使う。
規約：指定増強の等式。
使われ方：ホモトピーの基底側の恒等式。 -/
@[reassoc] theorem cechDegeneracy_base {n : ℕ} (i : Fin (n + 1)) :
    (Arrow.mk f).cechNerve.σ i ≫ WidePullback.base (fun _ : Fin (n + 2) ↦ f) =
      WidePullback.base (fun _ : Fin (n + 1) ↦ f) :=
  WidePullback.lift_base _ _ _ _

/-- 概要：細分比較は指定増強を保つ（論文 補題 3.2）。
方針：基底が恒等射であることと lift の公式を使う。
規約：元の比較射に対する等式。
使われ方：ホモトピーの両端の基底の検査。 -/
@[reassoc] theorem refinementCechMap_base (n : ℕ) :
    (refinementCechMap f g a ha).app (op ⦋n⦌) ≫
        WidePullback.base (fun _ : Fin (n + 1) ↦ g) =
      WidePullback.base (fun _ : Fin (n + 1) ↦ f) :=
  (WidePullback.lift_base _ _ _ _).trans (Category.comp_id _)

/-- 概要：細分ホモトピーの射は指定増強を保つ（論文 補題 3.2）。
方針：共通基底への lift の公式を使う。
規約：全ての切替位置を扱う。
使われ方：全ホモトピー恒等式の基底の検査。 -/
@[reassoc] theorem refinementCechHomotopyMap_base {n : ℕ} (i : Fin (n + 1)) :
    refinementCechHomotopyMap f g a b ha hb i ≫
        WidePullback.base (fun _ : Fin (n + 2) ↦ g) =
      WidePullback.base (fun _ : Fin (n + 1) ↦ f) :=
  WidePullback.lift_base _ _ _ _

/-- 概要：同じ基底上の二つの細分 Čech 比較は単体ホモトピック（論文 補題 3.2）。
方針：実際の切替座標の射を使い、全ての面射・退化射の恒等式を有限添字で検査する。
規約：二つの持ち上げの一致や群の作用は要求しない。
使われ方：細分・相互細分により比較写像の選択を除く。 -/
noncomputable def refinementCechHomotopy :
    SimplicialObject.Homotopy (refinementCechMap f g a ha) (refinementCechMap f g b hb) where
  h := refinementCechHomotopyMap f g a b ha hb
  h_zero_comp_δ_zero n := by
    apply WidePullback.hom_ext <;>
      dsimp only [Arrow.mk_hom, SimplexCategory.len_mk, unop_op]
    · intro j
      simp only [Category.assoc, cechFace_π, refinementCechHomotopyMap_π,
        cechMixIndex_zero, refinementCechCoordinate, ite_eq_right (by decide : ¬(1 : ℕ) = 0),
        refinementCechMap_π]
    · simp only [Category.assoc, cechFace_base, refinementCechHomotopyMap_base]
      exact (refinementCechMap_base f g b hb n).symm
  h_last_comp_δ_last n := by
    apply WidePullback.hom_ext <;>
      dsimp only [Arrow.mk_hom, SimplexCategory.len_mk, unop_op]
    · intro j
      simp only [Category.assoc, cechFace_π, refinementCechHomotopyMap_π,
        cechMixIndex_last, refinementCechCoordinate, ↓reduceIte, refinementCechMap_π]
    · simp only [Category.assoc, cechFace_base, refinementCechHomotopyMap_base]
      exact (refinementCechMap_base f g a ha n).symm
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply WidePullback.hom_ext <;>
      dsimp only [Arrow.mk_hom, SimplexCategory.len_mk, unop_op]
    · intro k
      simp only [Category.assoc, cechFace_π, refinementCechHomotopyMap_π, cechFace_coordinate]
      exact congrArg (refinementCechCoordinate f a b _) (cechMixIndex_face_before i j hij k)
    · simp only [Category.assoc, cechFace_base, refinementCechHomotopyMap_base]
      exact ((congrArg (_ ≫ ·) (refinementCechHomotopyMap_base f g a b ha hb j)).trans
        (cechFace_base f i)).symm
  h_succ_comp_δ_castSucc_succ j := by
    apply WidePullback.hom_ext <;>
      dsimp only [Arrow.mk_hom, SimplexCategory.len_mk, unop_op]
    · intro k
      simp only [Category.assoc, cechFace_π, refinementCechHomotopyMap_π]
      exact congrArg (refinementCechCoordinate f a b _) (cechMixIndex_face_middle j k)
    · simp only [Category.assoc, cechFace_base, refinementCechHomotopyMap_base]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply WidePullback.hom_ext <;>
      dsimp only [Arrow.mk_hom, SimplexCategory.len_mk, unop_op]
    · intro k
      simp only [Category.assoc, cechFace_π, refinementCechHomotopyMap_π, cechFace_coordinate]
      exact congrArg (refinementCechCoordinate f a b _) (cechMixIndex_face_after i j hji k)
    · simp only [Category.assoc, cechFace_base, refinementCechHomotopyMap_base]
      exact ((congrArg (_ ≫ ·) (refinementCechHomotopyMap_base f g a b ha hb j)).trans
        (cechFace_base f i)).symm
  h_comp_σ_castSucc_of_le i j hij := by
    apply WidePullback.hom_ext <;>
      dsimp only [Arrow.mk_hom, SimplexCategory.len_mk, unop_op]
    · intro k
      simp only [Category.assoc, cechDegeneracy_π, refinementCechHomotopyMap_π,
        cechDegeneracy_coordinate]
      exact congrArg (refinementCechCoordinate f a b _) (cechMixIndex_degeneracy_before i j hij k)
    · simp only [Category.assoc, cechDegeneracy_base, refinementCechHomotopyMap_base]
      exact ((congrArg (_ ≫ ·) (refinementCechHomotopyMap_base f g a b ha hb j.succ)).trans
        (cechDegeneracy_base f i)).symm
  h_comp_σ_succ_of_lt i j hji := by
    apply WidePullback.hom_ext <;>
      dsimp only [Arrow.mk_hom, SimplexCategory.len_mk, unop_op]
    · intro k
      simp only [Category.assoc, cechDegeneracy_π, refinementCechHomotopyMap_π,
        cechDegeneracy_coordinate]
      exact congrArg (refinementCechCoordinate f a b _) (cechMixIndex_degeneracy_after i j hji k)
    · simp only [Category.assoc, cechDegeneracy_base, refinementCechHomotopyMap_base]
      exact ((congrArg (_ ≫ ·) (refinementCechHomotopyMap_base f g a b ha hb j.castSucc)).trans
        (cechDegeneracy_base f i)).symm

end SerrePositivity.KST.Descent
