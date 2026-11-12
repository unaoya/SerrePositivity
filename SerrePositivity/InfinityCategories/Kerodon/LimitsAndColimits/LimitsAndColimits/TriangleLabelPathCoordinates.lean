module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutRightEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutStageReindex

/-!
概要：三対象の制御二胞体に使う、path の中間ラベルとパラメーター座標。
方針：零ラベルの最大点と、中間ラベルの点を含むかどうかを別々に読む。
規約：面・退化による添字変換を含む。元の二短辺が固定された構成に使う。
使われ方：全長 Hom の単体を、全次数で coherent 二胞体へ写すための有限座標。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 三対象のうち、最初の対象だけを零とする二値ラベル。 -/
def triangleZeroLabel {n : ℕ} (t : Fin (n + 1) →o Fin 3) : Fin (n + 1) →o Fin 2 where
  toFun i := if t i = 0 then 0 else 1
  monotone' := by
    intro i j hij
    have ht := t.monotone hij
    dsimp only
    split_ifs <;> omega

lemma triangleZeroLabel_zero {n : ℕ} (t : Fin (n + 1) →o Fin 3)
    {i : Fin (n + 1)} (hi : t i = 0) : triangleZeroLabel t i = 0 := by
  simp [triangleZeroLabel, hi]

/-- path に中間対象の点が現れれば一、現れなければ零。 -/
def trianglePathMiddle {n : ℕ} (t : Fin (n + 1) →o Fin 3) {i j : Fin (n + 1)}
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) : Fin 2 := by
  classical
  exact if ∃ k : Fin (n + 1), ULift.up k ∈ P.I ∧ t k = 1 then 1 else 0

lemma trianglePathMiddle_mono {n : ℕ} (t : Fin (n + 1) →o Fin 3) {i j : Fin (n + 1)}
    {P Q : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)}
    (h : P.I ⊆ Q.I) : trianglePathMiddle t P ≤ trianglePathMiddle t Q := by
  classical
  dsimp only [trianglePathMiddle]
  split_ifs with hp hq hq
  · exact le_rfl
  · obtain ⟨k, hk, ht⟩ := hp
    exact False.elim (hq ⟨k, h hk, ht⟩)
  · decide
  · exact le_rfl

/-- 中間対象の有無を path 圏から標準区間の頂点圏へ写す。 -/
def trianglePathMiddleFunctor {n : ℕ} (t : Fin (n + 1) →o Fin 3) (i j : Fin (n + 1)) :
    Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j) ⥤ ULift.{u} (Fin 2) where
  obj P := ULift.up (trianglePathMiddle t P)
  map f := homOfLE (trianglePathMiddle_mono t f.1.1.1)

/-- 中間対象の有無を標準区間として実現する。 -/
def trianglePathMiddleMap {n : ℕ} (t : Fin (n + 1) →o Fin 3) (i j : Fin (n + 1)) :
    nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶ Δ[1] :=
  nerveMap (trianglePathMiddleFunctor t i j) ≫ (stdSimplex.isoNerve 1).inv

/-- 零ラベルの最大座標と中間対象の有無を、同時に保持する座標射。 -/
def triangleLabelPathCoordinates {n : ℕ} (t : Fin (n + 1) →o Fin 3)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 1)) :
    nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶
      (Δ[1] : SSet.{u}) ⊗ Δ[n] :=
  CartesianMonoidalCategory.lift (trianglePathMiddleMap t i j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (triangleZeroLabel t) (triangleZeroLabel_zero t hi) j)

/-- 中間点の存在は、面・退化の全添字変換と厳密に可換。 -/
lemma trianglePathMiddle_image {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (t : Fin (n + 1) →o Fin 3) {i j : Fin (m + 1)}
    (P : Path (ULift.up i : ULift.{u} (Fin (m + 1))) (ULift.up j)) :
    trianglePathMiddle t (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutImage α P) = trianglePathMiddle (t.comp α) P := by
  classical
  have h : (∃ k, ULift.up k ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutImage α P).I ∧ t k = 1) ↔
      (∃ k, ULift.up k ∈ P.I ∧ (t.comp α) k = 1) := by
    constructor
    · rintro ⟨k, ⟨⟨l⟩, hl, he⟩, ht⟩
      have he' : α l = k := congrArg ULift.down he
      exact ⟨l, hl, by change t (α l) = 1; rw [he']; exact ht⟩
    · rintro ⟨k, hk, ht⟩
      exact ⟨α k, ⟨ULift.up k, hk, rfl⟩, ht⟩
  simp only [trianglePathMiddle, h]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
