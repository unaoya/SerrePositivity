module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：coherent な単体の path を最大の区間 path へ変形するための座標。
方針：時刻一の頂点以降を終点まで埋め、時刻零の部分は元の path の像を保つ。
規約：順序集合上の path の包含規約を使い、合成は集合の和集合。
使われ方：Kerodon §5.6（Tag 027M）、Proposition 4.6.7.23（Tag 01LW）、coherent な単体の局所的な strict 化。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：path の時刻一の頂点から後を区間で埋める。
方針：元の path の像に、時刻一の各頂点から終点までの区間を加える。
規約：A と t はともに単調写像。
使われ方：Kerodon §5.6（Tag 027M）、coherent な単体とその strict な射列の比較の Hom の座標。 -/
def coherentPathDeformation {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) {i j : J} (P : Path i j) : Path (A i) (A j) where
  I := A '' P.I ∪ {z | ∃ k ∈ P.I, t k = 1 ∧ A k ≤ z ∧ z ≤ A j}
  left := Or.inl ⟨i, P.left, rfl⟩
  right := Or.inl ⟨j, P.right, rfl⟩
  left_le z hz := by
    rcases hz with ⟨k, hk, rfl⟩ | ⟨k, hk, _, hkz, _⟩
    · exact A.monotone (P.left_le k hk)
    · exact (A.monotone (P.left_le k hk)).trans hkz
  le_right z hz := by
    rcases hz with ⟨k, hk, rfl⟩ | ⟨_, _, _, _, hzj⟩
    · exact A.monotone (P.le_right k hk)
    · exact hzj

/-- 概要：path の変形は元の path の包含に関して単調。
方針：元の像の点と追加区間の始点の証人をそのまま使う。
規約：端点を固定する。
使われ方：Kerodon §5.6（Tag 027M）、変形した Hom の nerve を取るための関手性。 -/
lemma coherentPathDeformation_mono {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) {i j : J} {P Q : Path i j} (h : P.I ⊆ Q.I) :
    (coherentPathDeformation A t P).I ⊆ (coherentPathDeformation A t Q).I := by
  rintro z (⟨k, hk, rfl⟩ | ⟨k, hk, ht, hkz, hzj⟩)
  · exact Or.inl ⟨k, h hk, rfl⟩
  · exact Or.inr ⟨k, h hk, ht, hkz, hzj⟩

/-- 概要：path の変形は恒等 path を保つ。
方針：同じ端点を持つ path の各点を端点で上下から挟む。
規約：変形の時刻の値は任意。
使われ方：Kerodon §2.4.3（Tag 00KM）、変形による豊穣関手の単位則。 -/
lemma coherentPathDeformation_id {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) (i : J) :
    coherentPathDeformation A t (𝟙 (⟨i⟩ : SimplicialThickening J)) =
      𝟙 (⟨A i⟩ : SimplicialThickening K) := by
  apply SimplicialThickening.Path.ext
  ext z
  change z ∈ (coherentPathDeformation A t (𝟙 (⟨i⟩ : SimplicialThickening J))).I ↔ z = A i
  constructor
  · intro hz
    exact le_antisymm (Path.le_right _ z hz) (Path.left_le _ z hz)
  · rintro rfl
    exact Path.left _

/-- 概要：path の変形は和集合による path の合成を保つ。
方針：追加区間の点を接合点の前後で分け、後半には時刻一の接合点を証人に取る。
規約：時刻の単調性により、一度時刻一になれば後続の時刻も一。
使われ方：Kerodon §2.4.3（Tag 00KM）、coherent な単体を変形する豊穣関手の合成則。 -/
lemma coherentPathDeformation_comp {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) {i j k : J} (P : Path i j) (Q : Path j k) :
    coherentPathDeformation A t
        (show (⟨i⟩ : SimplicialThickening J) ⟶ ⟨k⟩ from P ≫ Q) =
      (show (⟨A i⟩ : SimplicialThickening K) ⟶ ⟨A k⟩ from
        coherentPathDeformation A t P ≫ coherentPathDeformation A t Q) := by
  apply SimplicialThickening.Path.ext
  ext z
  change (z ∈ A '' (P.I ∪ Q.I) ∨
      ∃ l ∈ P.I ∪ Q.I, t l = 1 ∧ A l ≤ z ∧ z ≤ A k) ↔
    (z ∈ (coherentPathDeformation A t P).I ∨ z ∈ (coherentPathDeformation A t Q).I)
  constructor
  · rintro (⟨l, hl | hl, rfl⟩ | ⟨l, hl | hl, ht, hlz, hzk⟩)
    · exact Or.inl (Or.inl ⟨l, hl, rfl⟩)
    · exact Or.inr (Or.inl ⟨l, hl, rfl⟩)
    · by_cases hzj : z ≤ A j
      · exact Or.inl (Or.inr ⟨l, hl, ht, hlz, hzj⟩)
      · have htj : t j = 1 := by
          apply Fin.ext
          have h := t.monotone (P.le_right l hl)
          rw [ht] at h
          have hj := (t j).isLt
          change (1 : Fin 2).val ≤ (t j).val at h
          omega
        exact Or.inr (Or.inr ⟨j, Q.left, htj, le_of_not_ge hzj, hzk⟩)
    · exact Or.inr (Or.inr ⟨l, hl, ht, hlz, hzk⟩)
  · rintro ((⟨l, hl, rfl⟩ | ⟨l, hl, ht, hlz, hzj⟩) |
      (⟨l, hl, rfl⟩ | ⟨l, hl, ht, hlz, hzk⟩))
    · exact Or.inl ⟨l, Or.inl hl, rfl⟩
    · exact Or.inr ⟨l, Or.inl hl, ht, hlz, hzj.trans (A.monotone Q.le)⟩
    · exact Or.inl ⟨l, Or.inr hl, rfl⟩
    · exact Or.inr ⟨l, Or.inr hl, ht, hlz, hzk⟩

/-- 概要：path の変形は始域の単調写像による添字変換と可換。
方針：像の点と時刻一の区間の始点の証人を単調写像の像で対応させる。
規約：終点も同じ単調写像で写す。
使われ方：Kerodon §5.6（Tag 027M）、変形した coherent な単体の面・退化との整合性。 -/
lemma coherentPathDeformation_reindex {I J K : Type u}
    [LinearOrder I] [LinearOrder J] [LinearOrder K]
    (g : I →o J) (A : J →o K) (t : J →o Fin 2) {i j : I} (P : Path i j) :
    coherentPathDeformation (A.comp g) (t.comp g) P =
      coherentPathDeformation A t ((SimplicialThickening.functorMap g ⟨i⟩ ⟨j⟩).obj P) := by
  apply SimplicialThickening.Path.ext
  ext z
  change (z ∈ (A.comp g) '' P.I ∨
      ∃ k ∈ P.I, t (g k) = 1 ∧ A (g k) ≤ z ∧ z ≤ A (g j)) ↔
    (z ∈ A '' (g '' P.I) ∨
      ∃ k ∈ g '' P.I, t k = 1 ∧ A k ≤ z ∧ z ≤ A (g j))
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, ht, hkz, hzj⟩)
    · exact Or.inl ⟨g k, ⟨k, hk, rfl⟩, rfl⟩
    · exact Or.inr ⟨g k, ⟨k, hk, rfl⟩, ht, hkz, hzj⟩
  · rintro (⟨_, ⟨k, hk, rfl⟩, rfl⟩ | ⟨_, ⟨k, hk, rfl⟩, ht, hkz, hzj⟩)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr ⟨k, hk, ht, hkz, hzj⟩

/-- 概要：時刻零に固定した変形は元の path の通常の単調写像による像。
方針：時刻一の始点が存在しないので追加区間は空。
規約：端点は A の像。
使われ方：Kerodon §5.6（Tag 027M）、coherent な単体の変形の最初の端点。 -/
lemma coherentPathDeformation_zero {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) {i j : J} (P : Path i j) :
    coherentPathDeformation A (OrderHom.const J 0) P =
      (SimplicialThickening.functorMap A ⟨i⟩ ⟨j⟩).obj P := by
  apply SimplicialThickening.Path.ext
  ext z
  simp [coherentPathDeformation]

/-- 概要：時刻一に固定した変形の像は二端点間の全区間。
方針：元の始点を時刻一の区間の証人にし、逆は path の上下界を使う。
規約：最大の path の台を集合の区間として述べる。
使われ方：Kerodon §5.6（Tag 027M）、coherent な単体の変形の strict な終点の Hom。 -/
lemma coherentPathDeformation_one {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) {i j : J} (P : Path i j) :
    (coherentPathDeformation A (OrderHom.const J 1) P).I = Set.Icc (A i) (A j) := by
  ext z
  constructor
  · intro hz
    exact ⟨Path.left_le _ z hz, Path.le_right _ z hz⟩
  · rintro ⟨hiz, hzj⟩
    exact Or.inr ⟨i, P.left, rfl, hiz, hzj⟩

/-- 概要：対象写像が定値なら変形した path は恒等 path。
方針：同じ二端点の上下界によって全ての点をその定値に固定する。
規約：時刻写像 t は任意。
使われ方：Kerodon §5.6（Tag 027M）、単体の変形が各頂点を固定することの検証。 -/
lemma coherentPathDeformation_constant {J K : Type u} [LinearOrder J] [LinearOrder K]
    (a : K) (t : J →o Fin 2) {i j : J} (P : Path i j) :
    coherentPathDeformation (OrderHom.const J a) t P =
      𝟙 (⟨a⟩ : SimplicialThickening K) := by
  apply SimplicialThickening.Path.ext
  ext z
  change z ∈ (coherentPathDeformation (OrderHom.const J a) t P).I ↔ z = a
  constructor
  · intro hz
    exact le_antisymm (Path.le_right _ z hz) (Path.left_le _ z hz)
  · rintro rfl
    exact Path.left _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
