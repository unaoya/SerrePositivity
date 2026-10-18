module
public import SerrePositivity.KST.SConstruction.ZeroDirectionsRanges

/-! # 任意の多単体図式の零方向の像と交差
概要：零方向の像の分裂と交差の式を任意の多単体図式について証明する。
方針：添字のレトラクションと可換な零自己射を関手で写す。
規約：各段の可縮性は仮定しない。使われ方：一次を固定した残りの境界の弱可縮性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：指定した全方向を零に固定した core S の単体的図式。
方針：全方向の対角を零方向の自己関手と合成する。
規約：零方向を複数指定できる。使われ方：境界の交差の実現。 -/
def coordinateZeroDiagram {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  multiIndexDiagonal r ⋙ zeroDirectionsIndex s ⋙ M

/-- 概要：零方向を固定した図式から全方向の対角図式への自然変換。
方針：添字の包含を core S で写す。
規約：内部の単体方向も保持する。使われ方：境界の実現への包含。 -/
def coordinateZeroDiagramMap {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    coordinateZeroDiagram s M ⟶ multiIndexDiagonal r ⋙ M :=
  Functor.whiskerLeft (multiIndexDiagonal r)
    (Functor.whiskerRight (zeroDirectionsIndexNat s) M)

/-- 概要：零方向の実現から全反復実現への射。
方針：図式の自然変換の対角を取る。
規約：対角の Kan 性は仮定しない。使われ方：境界の単体集合としての像。 -/
def coordinateZeroInclusion {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    simplicialDiagonalFunctor.obj (coordinateZeroDiagram s M) ⟶ simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M) :=
  simplicialDiagonalFunctor.map (coordinateZeroDiagramMap s M)

/-- 概要：零方向の実現の包含は単射。
方針：各次数の包含に添字のレトラクションを写した左逆を合成する。
規約：有限集合は空でもよい。使われ方：境界の部分複体と交差。 -/
instance coordinateZeroInclusion_mono {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    Mono (coordinateZeroInclusion s M) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro x y h
  have hh := congrArg ((M.map
    (zeroDirectionsIndexRetraction s (fun _ => d))).app d) h
  change ((M.map ((zeroDirectionsIndexNat s).app (fun _ => d)) ≫
    M.map (zeroDirectionsIndexRetraction s (fun _ => d))).app d) x =
    ((M.map ((zeroDirectionsIndexNat s).app (fun _ => d)) ≫
    M.map (zeroDirectionsIndexRetraction s (fun _ => d))).app d) y at hh
  rw [← CategoryTheory.Functor.map_comp, zeroDirectionsIndexNat_retraction,
    CategoryTheory.Functor.map_id] at hh
  exact hh

/-- 概要：零方向の実現の包含への次数ごとのレトラクション。
方針：添字のレトラクションを core S の関手で写す。
規約：単体集合の射ではなく次数ごとの関数。使われ方：像の固定点判定。 -/
def coordinateZeroRetractionAt {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (x : (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).obj d) :
    (simplicialDiagonalFunctor.obj (coordinateZeroDiagram s M)).obj d :=
  (M.map (zeroDirectionsIndexRetraction s (fun _ => d))).app d x

/-- 概要：次数ごとのレトラクションは包含の左逆。
方針：添字の分裂の等式を core S で写す。
規約：全次数で成り立つ。使われ方：像の固定点判定。 -/
lemma coordinateZeroRetractionAt_leftInverse {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) :
    Function.LeftInverse (coordinateZeroRetractionAt s M d) ((coordinateZeroInclusion s M).app d) := by
  intro x
  change ((M.map ((zeroDirectionsIndexNat s).app (fun _ => d)) ≫
    M.map (zeroDirectionsIndexRetraction s (fun _ => d))).app d) x = x
  rw [← CategoryTheory.Functor.map_comp, zeroDirectionsIndexNat_retraction,
    CategoryTheory.Functor.map_id]
  rfl

/-- 概要：零方向の像への次数ごとの冪等作用。
方針：レトラクションで戻して包含する。
規約：固定点が零方向の像となる。使われ方：境界の交差。 -/
def coordinateZeroOperator {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (x : (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).obj d) :
    (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).obj d :=
  (coordinateZeroInclusion s M).app d (coordinateZeroRetractionAt s M d x)

/-- 概要：零方向の冪等作用は添字の自己射を写した作用。
方針：関手の合成則を使う。
規約：各単体での等号。使われ方：合併による作用の合成。 -/
lemma coordinateZeroOperator_eq_map {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (x : (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).obj d) :
    coordinateZeroOperator s M d x =
      (M.map (zeroDirectionsIndexEndomorphism s (fun _ => d))).app d x := by
  rw [zeroDirectionsIndexEndomorphism, CategoryTheory.Functor.map_comp]
  rfl

/-- 概要：零方向の合併の作用は二つの作用の合成。
方針：添字の自己射の合成則を写す。
規約：作用素は可換。使われ方：像の交差の証明。 -/
lemma coordinateZeroOperator_union {r : ℕ} (s t : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (x : (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).obj d) :
    coordinateZeroOperator (s ∪ t) M d x =
      coordinateZeroOperator t M d (coordinateZeroOperator s M d x) := by
  simp only [coordinateZeroOperator_eq_map]
  rw [zeroDirectionsIndexEndomorphism_union, CategoryTheory.Functor.map_comp]
  rfl

/-- 概要：指定した零方向を持つ部分の全反復実現内の像。
方針：単射な包含の range 部分複体を取る。
規約：全高次単体を保持する。使われ方：境界の合併。 -/
def coordinateZeroRange {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).Subcomplex := Subcomplex.range (coordinateZeroInclusion s M)

/-- 概要：零方向の像への所属は対応する冪等作用の固定点であることと同値。
方針：包含とレトラクションの分裂を使う。
規約：全単体での判定。使われ方：交差の計算。 -/
lemma mem_coordinateZeroRange_iff {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (x : (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).obj d) :
    x ∈ (coordinateZeroRange s M).obj d ↔ coordinateZeroOperator s M d x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact congrArg ((coordinateZeroInclusion s M).app d) (coordinateZeroRetractionAt_leftInverse s M d y)
  · intro hx
    exact ⟨coordinateZeroRetractionAt s M d x, hx⟩

/-- 概要：より多くの零方向を固定する像は小さくなる。
方針：合併の作用の固定点判定を使う。
規約：方向集合について反単調。使われ方：交差の包含。 -/
lemma coordinateZeroRange_antitone {r : ℕ} {s t : Finset (Fin r)} (hst : s ⊆ t)
    (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) : coordinateZeroRange t M ≤ coordinateZeroRange s M := by
  intro d x hx
  apply (mem_coordinateZeroRange_iff s M d x).2
  have ht := (mem_coordinateZeroRange_iff t M d x).1 hx
  calc
    coordinateZeroOperator s M d x = coordinateZeroOperator s M d (coordinateZeroOperator t M d x) :=
      congrArg (coordinateZeroOperator s M d) ht.symm
    _ = coordinateZeroOperator (t ∪ s) M d x := (coordinateZeroOperator_union t s M d x).symm
    _ = coordinateZeroOperator t M d x := by rw [Finset.union_eq_left.mpr hst]
    _ = x := ht

/-- 概要：零方向の二つの像の交差は方向集合の合併の像。
方針：固定点判定と可換な冪等作用の合成則を使う。
規約：単体集合の部分複体としての厳密な等式。使われ方：境界交差の全管理。 -/
lemma coordinateZeroRange_union {r : ℕ} (s t : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    coordinateZeroRange (s ∪ t) M = coordinateZeroRange s M ⊓ coordinateZeroRange t M := by
  apply le_antisymm
  · exact le_inf (coordinateZeroRange_antitone Finset.subset_union_left M)
      (coordinateZeroRange_antitone Finset.subset_union_right M)
  · intro d x hx
    apply (mem_coordinateZeroRange_iff (s ∪ t) M d x).2
    rw [coordinateZeroOperator_union, (mem_coordinateZeroRange_iff s M d x).1 hx.1,
      (mem_coordinateZeroRange_iff t M d x).1 hx.2]


end SerrePositivity.KST.SConstruction
