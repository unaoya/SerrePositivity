module
public import SerrePositivity.KST.SConstruction.ZeroDirections

/-! # 零方向の実現の像と交差
概要：零方向の像を部分複体として取り、交差を固定方向の合併で表す。
方針：次数ごとの可換な冪等作用素の固定点で像を判定する。
規約：レトラクション自体の自然性は要求しない。使われ方：境界の有限合併。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：一座標の零段への射影の自己射。
方針：次数ごとのレトラクションの後で包含を合成する。
規約：自然変換とは主張しない。使われ方：冪等作用素の積。 -/
def zeroCoordinateEndomorphism {r : ℕ} (i : Fin r) (b : Bool) (d : Fin r → SimplexCategoryᵒᵖ) :
    d i ⟶ d i := zeroCoordinateRetraction i b d ≫ (zeroCoordinateNat i b).app d

/-- 概要：一座標の二つの零固定は論理和に合成する。
方針：二つの真偽値について場合分けする。
規約：方向を固定する順序に依存しない。使われ方：境界の交差の計算。 -/
lemma zeroCoordinateEndomorphism_or {r : ℕ} (i : Fin r) (a b : Bool)
    (d : Fin r → SimplexCategoryᵒᵖ) :
    zeroCoordinateEndomorphism i (a || b) d =
      zeroCoordinateEndomorphism i a d ≫ zeroCoordinateEndomorphism i b d := by
  cases a <;> cases b
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · exact (Category.comp_id _).symm
  · rfl

/-- 概要：指定した零方向への次数ごとの自己射。
方針：全座標のレトラクションと包含を合成する。
規約：次数ごとの冪等作用素。使われ方：零方向の像の固定点判定。 -/
def zeroDirectionsIndexEndomorphism {r : ℕ} (s : Finset (Fin r))
    (d : Fin r → SimplexCategoryᵒᵖ) : d ⟶ d :=
  zeroDirectionsIndexRetraction s d ≫ (zeroDirectionsIndexNat s).app d

/-- 概要：零方向の合併は自己射の合成に対応する。
方針：各座標で論理和の合成則を使う。
規約：順序は任意。使われ方：像の交差。 -/
lemma zeroDirectionsIndexEndomorphism_union {r : ℕ} (s t : Finset (Fin r))
    (d : Fin r → SimplexCategoryᵒᵖ) :
    zeroDirectionsIndexEndomorphism (s ∪ t) d =
      zeroDirectionsIndexEndomorphism s d ≫ zeroDirectionsIndexEndomorphism t d := by
  funext i
  change zeroCoordinateEndomorphism i (decide (i ∈ s ∪ t)) d =
    zeroCoordinateEndomorphism i (decide (i ∈ s)) d ≫ zeroCoordinateEndomorphism i (decide (i ∈ t)) d
  have he : decide (i ∈ s ∪ t) = (decide (i ∈ s) || decide (i ∈ t)) := by simp
  rw [he]
  exact zeroCoordinateEndomorphism_or i _ _ d

/-- 概要：零方向の実現の包含への次数ごとのレトラクション。
方針：添字のレトラクションを core S の関手で写す。
規約：単体集合の射ではなく次数ごとの関数。使われ方：像の固定点判定。 -/
def zeroDirectionsRetractionAt {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (x : (multiDiagonalCoreSConstruction r X).obj d) :
    (simplicialDiagonalFunctor.obj (zeroDirectionsDiagram s X)).obj d :=
  ((multiCoreSConstruction r X).map (zeroDirectionsIndexRetraction s (fun _ => d))).app d x

/-- 概要：次数ごとのレトラクションは包含の左逆。
方針：添字の分裂の等式を core S で写す。
規約：全次数で成り立つ。使われ方：像の固定点判定。 -/
lemma zeroDirectionsRetractionAt_leftInverse {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) :
    Function.LeftInverse (zeroDirectionsRetractionAt s X d) ((zeroDirectionsInclusion s X).app d) := by
  intro x
  change (((multiCoreSConstruction r X).map ((zeroDirectionsIndexNat s).app (fun _ => d)) ≫
    (multiCoreSConstruction r X).map (zeroDirectionsIndexRetraction s (fun _ => d))).app d) x = x
  rw [← CategoryTheory.Functor.map_comp, zeroDirectionsIndexNat_retraction,
    CategoryTheory.Functor.map_id]
  rfl

/-- 概要：零方向の像への次数ごとの冪等作用。
方針：レトラクションで戻して包含する。
規約：固定点が零方向の像となる。使われ方：境界の交差。 -/
def zeroDirectionsOperator {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (x : (multiDiagonalCoreSConstruction r X).obj d) :
    (multiDiagonalCoreSConstruction r X).obj d :=
  (zeroDirectionsInclusion s X).app d (zeroDirectionsRetractionAt s X d x)

/-- 概要：零方向の冪等作用は添字の自己射を写した作用。
方針：関手の合成則を使う。
規約：各単体での等号。使われ方：合併による作用の合成。 -/
lemma zeroDirectionsOperator_eq_map {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (x : (multiDiagonalCoreSConstruction r X).obj d) :
    zeroDirectionsOperator s X d x =
      ((multiCoreSConstruction r X).map (zeroDirectionsIndexEndomorphism s (fun _ => d))).app d x := by
  rw [zeroDirectionsIndexEndomorphism, CategoryTheory.Functor.map_comp]
  rfl

/-- 概要：零方向の合併の作用は二つの作用の合成。
方針：添字の自己射の合成則を写す。
規約：作用素は可換。使われ方：像の交差の証明。 -/
lemma zeroDirectionsOperator_union {r : ℕ} (s t : Finset (Fin r)) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (x : (multiDiagonalCoreSConstruction r X).obj d) :
    zeroDirectionsOperator (s ∪ t) X d x =
      zeroDirectionsOperator t X d (zeroDirectionsOperator s X d x) := by
  simp only [zeroDirectionsOperator_eq_map]
  rw [zeroDirectionsIndexEndomorphism_union, CategoryTheory.Functor.map_comp]
  rfl

/-- 概要：指定した零方向を持つ部分の全反復実現内の像。
方針：単射な包含の range 部分複体を取る。
規約：全高次単体を保持する。使われ方：境界の合併。 -/
def zeroDirectionsRange {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    (multiDiagonalCoreSConstruction r X).Subcomplex := Subcomplex.range (zeroDirectionsInclusion s X)

/-- 概要：零方向の像への所属は対応する冪等作用の固定点であることと同値。
方針：包含とレトラクションの分裂を使う。
規約：全単体での判定。使われ方：交差の計算。 -/
lemma mem_zeroDirectionsRange_iff {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (x : (multiDiagonalCoreSConstruction r X).obj d) :
    x ∈ (zeroDirectionsRange s X).obj d ↔ zeroDirectionsOperator s X d x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact congrArg ((zeroDirectionsInclusion s X).app d) (zeroDirectionsRetractionAt_leftInverse s X d y)
  · intro hx
    exact ⟨zeroDirectionsRetractionAt s X d x, hx⟩

/-- 概要：より多くの零方向を固定する像は小さくなる。
方針：合併の作用の固定点判定を使う。
規約：方向集合について反単調。使われ方：交差の包含。 -/
lemma zeroDirectionsRange_antitone {r : ℕ} {s t : Finset (Fin r)} (hst : s ⊆ t)
    (X : StableModel.{u}) : zeroDirectionsRange t X ≤ zeroDirectionsRange s X := by
  intro d x hx
  apply (mem_zeroDirectionsRange_iff s X d x).2
  have ht := (mem_zeroDirectionsRange_iff t X d x).1 hx
  calc
    zeroDirectionsOperator s X d x = zeroDirectionsOperator s X d (zeroDirectionsOperator t X d x) :=
      congrArg (zeroDirectionsOperator s X d) ht.symm
    _ = zeroDirectionsOperator (t ∪ s) X d x := (zeroDirectionsOperator_union t s X d x).symm
    _ = zeroDirectionsOperator t X d x := by rw [Finset.union_eq_left.mpr hst]
    _ = x := ht

/-- 概要：零方向の二つの像の交差は方向集合の合併の像。
方針：固定点判定と可換な冪等作用の合成則を使う。
規約：単体集合の部分複体としての厳密な等式。使われ方：境界交差の全管理。 -/
lemma zeroDirectionsRange_union {r : ℕ} (s t : Finset (Fin r)) (X : StableModel.{u}) :
    zeroDirectionsRange (s ∪ t) X = zeroDirectionsRange s X ⊓ zeroDirectionsRange t X := by
  apply le_antisymm
  · exact le_inf (zeroDirectionsRange_antitone Finset.subset_union_left X)
      (zeroDirectionsRange_antitone Finset.subset_union_right X)
  · intro d x hx
    apply (mem_zeroDirectionsRange_iff (s ∪ t) X d x).2
    rw [zeroDirectionsOperator_union, (mem_zeroDirectionsRange_iff s X d x).1 hx.1,
      (mem_zeroDirectionsRange_iff t X d x).1 hx.2]

end SerrePositivity.KST.SConstruction
