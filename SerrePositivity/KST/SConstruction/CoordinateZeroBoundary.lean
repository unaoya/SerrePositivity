module
public import SerrePositivity.KST.SConstruction.CoordinateZeroRanges
public import SerrePositivity.KST.SConstruction.ZeroBoundary

/-! # 任意の多単体図式の零境界の弱可縮性
概要：非空の零方向の各交差が各段で可縮 Kan なら、零境界の有限合併は弱可縮。
方針：対角定理と range の同型、交差の式と合併の pushout で帰納する。
規約：各段の条件を明示し、対角の Kan 性は要求しない。使われ方：一次方向の境界商。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：非空の零方向を固定した各段が可縮 Kan である条件。
方針：全ての交差と全ての次数を量化する。
規約：この条件は適用先で証明する。使われ方：有限合併の弱可縮性の入力。 -/
def CoordinateZeroContractible {r : ℕ} (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) : Prop :=
  ∀ (s : Finset (Fin r)), s.Nonempty → ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((coordinateZeroDiagram s M).obj d)

/-- 概要：零方向の図式から一点の定値図式への自然変換。
方針：各段で終対象への一意な射を使う。
規約：内部の単体方向も保持する。使われ方：対角の比較。 -/
def coordinateZeroDiagramToPoint {r : ℕ} (s : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    coordinateZeroDiagram s M ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (𝟙_ SSet.{u}) where
  app _d := toUnit _
  naturality {_d _e} _f := isTerminalTensorUnit.hom_ext _ _

/-- 概要：非空の零方向の実現は anodyne 局所化で一点と同値。
方針：各行の可縮 Kan 複体からの射の可逆性を対角へ移す。
規約：モデル構造を仮定しない。使われ方：各境界交差の弱可縮性。 -/
lemma coordinateZeroRealization_toPoint_localized_isIso {r : ℕ} (s : Finset (Fin r))
    (hs : s.Nonempty) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (hM : CoordinateZeroContractible M) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (simplicialDiagonalFunctor.obj (coordinateZeroDiagram s M)))) := by
  have hi (d : SimplexCategoryᵒᵖ) :
      IsIso (AnodyneHomotopy.anodyneQ.map ((coordinateZeroDiagramToPoint s M).app d)) := by
    have := trivialKanFibration_toUnit_of_contractible (hM s hs d)
    exact map_isIso_of_trivialKanFibration AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions)
        (toUnit ((coordinateZeroDiagram s M).obj d))
  exact SerrePositivity.BisimplicialModel.localized_diagonal_map (coordinateZeroDiagramToPoint s M) hi


/-- 概要：非空の零方向の像から一点への射は局所化で可逆。
方針：単射の源と range の同型を通じて実現の弱可縮性を移す。
規約：部分複体の像そのものについての主張。使われ方：有限合併の初期段階。 -/
lemma coordinateZeroRange_toPoint_localized_isIso {r : ℕ} (s : Finset (Fin r))
    (hs : s.Nonempty) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (hM : CoordinateZeroContractible M) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (coordinateZeroRange s M : SSet.{u}))) := by
  let Q := AnodyneHomotopy.anodyneQ
  let a := Subcomplex.toRange (coordinateZeroInclusion s M)
  have ha : IsIso (Q.map a) := inferInstance
  have hh : IsIso (Q.map a ≫ Q.map (toUnit (coordinateZeroRange s M : SSet.{u}))) := by
    have he : a ≫ toUnit (coordinateZeroRange s M : SSet.{u}) =
        toUnit (simplicialDiagonalFunctor.obj (coordinateZeroDiagram s M)) := isTerminalTensorUnit.hom_ext _ _
    rw [← Q.map_comp, he]
    exact coordinateZeroRealization_toPoint_localized_isIso s hs M hM
  exact (isIso_comp_left_iff _ _).1 hh

/-- 概要：追加で固定した零方向を持つ境界の有限合併。
方針：各選択方向を固定する像を格子の有限上限で合わせる。
規約：t は全ての部分に共通する零方向。使われ方：交差を含む帰納。 -/
def coordinateZeroBoundary {r : ℕ} (s t : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    (simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ M)).Subcomplex := s.sup (fun i => coordinateZeroRange (insert i t) M)

/-- 概要：一方向を合併に加えると一つの像との上限になる。
方針：有限上限の挿入の式を使う。
規約：方向の重複は許す。使われ方：境界の有限帰納。 -/
lemma coordinateZeroBoundary_insert {r : ℕ} (i : Fin r) (s t : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    coordinateZeroBoundary (insert i s) t M =
      coordinateZeroRange (insert i t) M ⊔ coordinateZeroBoundary s t M := by
  simp only [coordinateZeroBoundary, Finset.sup_insert]

/-- 概要：一方向の像と境界の交差は、共通零方向にその方向を加えた境界。
方針：有限合併について帰納し、像の交差の計算と分配則を使う。
規約：部分複体の厳密な等号。使われ方：合併の弱可縮性。 -/
lemma coordinateZeroBoundary_inf {r : ℕ} (i : Fin r) (s t : Finset (Fin r)) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    coordinateZeroRange (insert i t) M ⊓ coordinateZeroBoundary s t M =
      coordinateZeroBoundary s (insert i t) M := by
  induction s using Finset.induction_on with
  | empty => simp [coordinateZeroBoundary]
  | @insert j s hjs ih =>
    rw [coordinateZeroBoundary_insert]
    have hd := subcomplex_inf_sup (coordinateZeroRange (insert i t) M)
      (coordinateZeroRange (insert j t) M) (coordinateZeroBoundary s t M)
    rw [hd]
    rw [ih, coordinateZeroBoundary_insert]
    congr 1
    rw [← coordinateZeroRange_union]
    congr 1
    ext k
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto

/-- 概要：非空の零方向の境界の有限合併は弱可縮。
方針：全交差を同じ形の境界で表し、二つの部分と交差の pushout 比較で帰納する。
規約：共通の固定方向 t は空でもよい。使われ方：fat wedge 全体の collapse。 -/
lemma coordinateZeroBoundary_toPoint_localized_isIso {r : ℕ} (s t : Finset (Fin r))
    (hs : s.Nonempty) (M : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u})
    (hM : CoordinateZeroContractible M) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (coordinateZeroBoundary s t M : SSet.{u}))) := by
  induction s using Finset.induction_on generalizing t with
  | empty => exact False.elim (Finset.not_nonempty_empty hs)
  | @insert i s his ih =>
    by_cases hse : s = ∅
    · subst s
      have he : coordinateZeroBoundary (insert i ∅) t M = coordinateZeroRange (insert i t) M := by
        unfold coordinateZeroBoundary
        rw [Finset.insert_empty]
        exact Finset.sup_singleton
      rw [he]
      exact coordinateZeroRange_toPoint_localized_isIso (insert i t) (Finset.insert_nonempty _ _) M hM
    · have hsn : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hse
      rw [coordinateZeroBoundary_insert]
      apply subcomplex_sup_toPoint_localized_isIso
      · exact coordinateZeroRange_toPoint_localized_isIso _ (Finset.insert_nonempty _ _) M hM
      · exact ih t hsn
      · rw [coordinateZeroBoundary_inf]
        exact ih (insert i t) hsn


end SerrePositivity.KST.SConstruction
