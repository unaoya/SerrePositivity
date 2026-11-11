module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedRecoverIndex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedReadData

/-! # 線形族からの右 pinched 単体データの再構成

概要：最終点を含む成分を線形族から取り、先頭面を単位と零で埋める。
方針：先頭集合を回復して次数を合わせ、両端の対象を等式で移送する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形表示の逆写像のデータ部分。
このファイルではまだ全単体方程式を主張しない。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：再構成する単体の対象族は、最終点だけ y、それ以外は x。
方針：最終点との等式で二つに分ける。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形族からの単体の対象。 -/
def reconstructObj (x y : D) {n : ℕ} (i : Fin (n + 2)) : D :=
  if i = Fin.last (n + 1) then y else x

/-- 概要：最終点以外の再構成対象は x。
方針：対象族の非最終点の分岐を評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：先頭面と斉次成分の始点。 -/
lemma reconstructObj_of_ne_last (x y : D) {n : ℕ} {i : Fin (n + 2)}
    (hi : i ≠ Fin.last (n + 1)) : reconstructObj x y i = x := by
  simp only [reconstructObj, ite_eq_right hi]

/-- 概要：最終点の再構成対象は y。
方針：対象族の最終点の分岐を評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：線形成分の終点。 -/
lemma reconstructObj_of_eq_last (x y : D) {n : ℕ} {i : Fin (n + 2)}
    (hi : i = Fin.last (n + 1)) : reconstructObj x y i = y := by
  simp only [reconstructObj, ite_eq_left hi]

/-- 概要：先頭埋め込みの再構成対象は x。
方針：先頭点が最終点より小さいことを使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：定値先頭面との比較。 -/
lemma reconstructObj_castSucc (x y : D) {n : ℕ} (i : Fin (n + 1)) :
    reconstructObj x y i.castSucc = x :=
  reconstructObj_of_ne_last x y (ne_of_lt (Fin.castSucc_lt_last i))

namespace LinearData

variable {x y : D}

/-- 概要：任意の線形族から先頭面が単位・零である単体データを作る。
方針：終点が最終点なら線形族の先頭集合の成分、先頭だけの二点なら単位、それ以外なら零を取る。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形解からの単体への逆構成。 -/
def toSimplexData {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1) where
  obj := reconstructObj x y
  hom I a b k hI ha hb hk := by
    have han : a ≠ Fin.last (n + 1) := by rw [ha]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last I hI
    by_cases hbLast : b = Fin.last (n + 1)
    · have hLast : Fin.last (n + 1) ∈ I := hbLast ▸ (show b ∈ I by rw [hb]; exact I.max'_mem _)
      have hhead := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_nonempty hI hLast
      have hdeg : k = 1 - ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I).card : ℤ) := by
        have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withoutLast I hLast
        omega
      exact cast (by rw [reconstructObj_of_ne_last x y han, reconstructObj_of_eq_last x y hbLast])
        (f.component (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I) k hhead hdeg)
    · by_cases hc : I.card = 2
      · have hk0 : k = 0 := by omega
        exact cast (by
          rw [reconstructObj_of_ne_last x y han, reconstructObj_of_ne_last x y hbLast, hk0])
          (unitElement A x).val
      · exact 0

/-- 概要：終点が最終点の場合、再構成成分は線形族の先頭集合の成分と異種等号で一致する。
方針：最終点の分岐を評価し、対象の移送の cast を取り除く。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：終端を含む方程式と逆則。 -/
lemma toSimplexData_hom_last {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbLast : b = Fin.last (n + 1)) :
    HEq (f.toSimplexData.hom I a b k hI ha hb hk)
      (f.component (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I) k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_nonempty hI
        (hbLast ▸ (show b ∈ I by rw [hb]; exact I.max'_mem _))) (by
          have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withoutLast I (hbLast ▸ (show b ∈ I by rw [hb]; exact I.max'_mem _))
          omega)) := by
  simp only [toSimplexData, dite_eq_left hbLast]
  exact cast_heq _ _

/-- 概要：終点が最終点でない二点集合の再構成成分は単位。
方針：先頭面の二点の分岐を評価し、対象と次数の cast を取り除く。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：先頭面の辺。 -/
lemma toSimplexData_hom_unit {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbLast : b ≠ Fin.last (n + 1)) (hc : I.card = 2) :
    HEq (f.toSimplexData.hom I a b k hI ha hb hk) (unitElement A x).val := by
  simp only [toSimplexData, dite_eq_right hbLast, dite_eq_left hc]
  exact cast_heq _ _

/-- 概要：最終点でない終点を持つ高次の再構成成分は零。
方針：先頭面の高次成分の零の分岐を評価する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：先頭面の高次成分。 -/
lemma toSimplexData_hom_zero {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbLast : b ≠ Fin.last (n + 1)) (hc : I.card ≠ 2) :
    f.toSimplexData.hom I a b k hI ha hb hk = 0 := by
  simp only [toSimplexData, dite_eq_right hbLast, dite_eq_right hc]

/-- 概要：再構成したデータの全終端成分を回収すると元の線形族に戻る。
方針：最終点の分岐の計算と先頭集合の往復を使い、各成分の異種等号を合成する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形表示の片側の逆則のデータ部分。 -/
lemma toSimplexData_toPinchedLinearData {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) :
    f.toSimplexData.toPinchedLinearData x y (reconstructObj_castSucc x y)
      (reconstructObj_of_eq_last x y rfl) = f := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change k = 1 - (J.card : ℤ) at hk
  change (f.toSimplexData.toPinchedLinearData x y _ _).component J k hJ hk = f.component J k hJ hk
  apply eq_of_heq
  refine (f.toSimplexData.toPinchedLinearData_component_heq x y _ _ J k hJ hk).trans ?_
  refine (f.toSimplexData_hom_last (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega) rfl).trans ?_
  apply heq_of_eq
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component
  congr 1
  apply Subtype.ext
  exact Prod.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_withLast J) rfl

end LinearData

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
