module
public import SerrePositivity.KST.SConstruction.ReducedMultiRealization

/-! # 指定した S 方向を零次数に固定する添字
概要：有限個の方向を零に固定した部分図式と全図式への包含を構成する。
方針：各座標の定値関手と零段の退化を積圏で束ねる。
規約：零方向の選択は有限集合で保持する。使われ方：反復実現の境界の合併。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：一座標を零に固定するか、そのまま評価する関手。
方針：真偽値による二つの関手の定義。
規約：依存する射の型を各場合で厳密に保持する。使われ方：零方向の積。 -/
def zeroCoordinateFunctor {r : ℕ} (i : Fin r) : Bool → ((Fin r → SimplexCategoryᵒᵖ) ⥤ SimplexCategoryᵒᵖ)
  | true => (Functor.const _).obj (Opposite.op ⦋0⦌)
  | false => Pi.eval (fun _ : Fin r => SimplexCategoryᵒᵖ) i

/-- 概要：零固定した一座標から元の座標への自然変換。
方針：零段の退化または恒等射を使う。
規約：真偽値を明示する。使われ方：全方向の包含の積。 -/
def zeroCoordinateNat {r : ℕ} (i : Fin r) : (b : Bool) →
    zeroCoordinateFunctor i b ⟶ Pi.eval (fun _ : Fin r => SimplexCategoryᵒᵖ) i
  | true => {
      app d := (SimplexCategory.const (d i).unop ⦋0⦌ 0).op
      naturality {_d _e} _f := by
        apply Quiver.Hom.unop_inj
        exact @Subsingleton.elim ((_e i).unop ⟶ ⦋0⦌) inferInstance _ _ }
  | false => 𝟙 _

/-- 概要：零固定した一座標の包含に対する次数ごとのレトラクション。
方針：最初の頂点または恒等射を使う。
規約：自然性を要求しない。使われ方：包含の単射性。 -/
def zeroCoordinateRetraction {r : ℕ} (i : Fin r) : (b : Bool) →
    (d : Fin r → SimplexCategoryᵒᵖ) → d i ⟶ (zeroCoordinateFunctor i b).obj d
  | true, d => (SimplexCategory.const ⦋0⦌ (d i).unop 0).op
  | false, d => 𝟙 (d i)

/-- 概要：一座標の包含とレトラクションは恒等に合成する。
方針：零次数の自己射の一意性を使う。
規約：厳密な等号。使われ方：全方向の単射性。 -/
lemma zeroCoordinateNat_retraction {r : ℕ} (i : Fin r) (b : Bool)
    (d : Fin r → SimplexCategoryᵒᵖ) :
    (zeroCoordinateNat i b).app d ≫ zeroCoordinateRetraction i b d =
      𝟙 ((zeroCoordinateFunctor i b).obj d) := by
  cases b with
  | false => exact Category.id_comp _
  | true =>
    apply Quiver.Hom.unop_inj
    exact @Subsingleton.elim (⦋0⦌ ⟶ ⦋0⦌) inferInstance _ _

/-- 概要：指定した方向を零次数へ置き換える自己関手。
方針：各座標で零固定または評価を選び、積に束ねる。
規約：指定外の方向はそのまま。使われ方：境界の各交差の添字。 -/
def zeroDirectionsIndex {r : ℕ} (s : Finset (Fin r)) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ (Fin r → SimplexCategoryᵒᵖ) :=
  Functor.pi' (fun i => zeroCoordinateFunctor i (decide (i ∈ s)))

/-- 概要：零方向を固定する添字から元の添字への自然な射。
方針：一座標の包含を積に束ねる。
規約：全単体作用に自然。使われ方：境界の包含。 -/
def zeroDirectionsIndexNat {r : ℕ} (s : Finset (Fin r)) : zeroDirectionsIndex s ⟶ 𝟭 _ :=
  NatTrans.pi' (fun i => zeroCoordinateNat i (decide (i ∈ s)))

/-- 概要：各多次数で零方向の包含に対するレトラクションを選ぶ。
方針：各座標のレトラクションを積に束ねる。
規約：多次数について自然とは主張しない。使われ方：包含の単射性。 -/
def zeroDirectionsIndexRetraction {r : ℕ} (s : Finset (Fin r))
    (d : Fin r → SimplexCategoryᵒᵖ) : d ⟶ (zeroDirectionsIndex s).obj d :=
  fun i => zeroCoordinateRetraction i (decide (i ∈ s)) d

/-- 概要：零方向の包含とレトラクションの合成は恒等。
方針：一座標の恒等を積で使う。
規約：多次数ごとの厳密な等号。使われ方：全段の単射。 -/
lemma zeroDirectionsIndexNat_retraction {r : ℕ} (s : Finset (Fin r))
    (d : Fin r → SimplexCategoryᵒᵖ) :
    (zeroDirectionsIndexNat s).app d ≫ zeroDirectionsIndexRetraction s d =
      𝟙 ((zeroDirectionsIndex s).obj d) := by
  funext i
  exact zeroCoordinateNat_retraction i (decide (i ∈ s)) d

/-- 概要：指定した全方向を零に固定した core S の単体的図式。
方針：全方向の対角を零方向の自己関手と合成する。
規約：零方向を複数指定できる。使われ方：境界の交差の実現。 -/
def zeroDirectionsDiagram {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  multiIndexDiagonal r ⋙ zeroDirectionsIndex s ⋙ multiCoreSConstruction r X

/-- 概要：零方向を固定した図式から全方向の対角図式への自然変換。
方針：添字の包含を core S で写す。
規約：内部の単体方向も保持する。使われ方：境界の実現への包含。 -/
def zeroDirectionsDiagramMap {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    zeroDirectionsDiagram s X ⟶ (multiDiagonalDiagramFunctor r).obj X :=
  Functor.whiskerLeft (multiIndexDiagonal r)
    (Functor.whiskerRight (zeroDirectionsIndexNat s) (multiCoreSConstruction r X))

/-- 概要：零方向の実現から全反復実現への射。
方針：図式の自然変換の対角を取る。
規約：対角の Kan 性は仮定しない。使われ方：境界の単体集合としての像。 -/
def zeroDirectionsInclusion {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    simplicialDiagonalFunctor.obj (zeroDirectionsDiagram s X) ⟶ multiDiagonalCoreSConstruction r X :=
  simplicialDiagonalFunctor.map (zeroDirectionsDiagramMap s X)

/-- 概要：零方向の実現の包含は単射。
方針：各次数の包含に添字のレトラクションを写した左逆を合成する。
規約：有限集合は空でもよい。使われ方：境界の部分複体と交差。 -/
instance zeroDirectionsInclusion_mono {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    Mono (zeroDirectionsInclusion s X) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro x y h
  have hh := congrArg (((multiCoreSConstruction r X).map
    (zeroDirectionsIndexRetraction s (fun _ => d))).app d) h
  change (((multiCoreSConstruction r X).map ((zeroDirectionsIndexNat s).app (fun _ => d)) ≫
    (multiCoreSConstruction r X).map (zeroDirectionsIndexRetraction s (fun _ => d))).app d) x =
    (((multiCoreSConstruction r X).map ((zeroDirectionsIndexNat s).app (fun _ => d)) ≫
    (multiCoreSConstruction r X).map (zeroDirectionsIndexRetraction s (fun _ => d))).app d) y at hh
  rw [← CategoryTheory.Functor.map_comp, zeroDirectionsIndexNat_retraction,
    CategoryTheory.Functor.map_id] at hh
  exact hh

/-- 概要：一つ以上の方向を零に固定すれば各段は可縮 Kan 複体。
方針：指定集合内の一方向に既存の零方向の可縮性を適用する。
規約：固定外の次数は任意。使われ方：境界の交差の対角の弱可縮性。 -/
lemma zeroDirectionsDiagram_isContractibleKan {r : ℕ} (s : Finset (Fin r)) (hs : s.Nonempty)
    (X : StableModel.{u}) (d : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((zeroDirectionsDiagram s X).obj d) := by
  obtain ⟨i, hi⟩ := hs
  apply multiCoreSConstruction_isContractibleKan_of_zero_coordinate r X
    ((zeroDirectionsIndex s).obj (fun _ => d)) i
  change (Opposite.unop ((zeroCoordinateFunctor i (decide (i ∈ s))).obj (fun _ => d))).len = 0
  have he : decide (i ∈ s) = true := by simp [hi]
  rw [he]
  rfl

end SerrePositivity.KST.SConstruction
