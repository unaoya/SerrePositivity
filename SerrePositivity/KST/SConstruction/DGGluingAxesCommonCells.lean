module
public import SerrePositivity.KST.SConstruction.DGGluingAxesCofiberCellImages
public import SerrePositivity.KST.SConstruction.DGSimplexCommonUniverse

/-! # 同じ二軸二セルの共通宇宙での整合
概要：元の上下二セルを共通対象宇宙へ移し、同じ対角と Yoneda 像を保持する。
方針：実 dg 単体の面との可換性と、宇宙の上げ下げの厳密な回収を使う。
規約：両セルの元の二射を保持。使われ方：元の共通宇宙 dg nerve の cofiber 四角形。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
/-- 元の gluing の対象宇宙だけを、代表加群と同じ宇宙へ上げる。 -/
abbrev DGGluingAxesCommonUniverse := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max u (max v w), max (u + 1) (max v w)} G

/-- 同じ全 Hom 複体を保ち、元の gluing 対象ラベルだけを上げる実 dg 関手。 -/
def dgGluingAxesCommonUp : DGFunctor R G (DGGluingAxesCommonUniverse R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R G

local notation "GG" => DGGluingAxesCommonUniverse R C D M
local notation "U" => dgGluingAxesCommonUp R C D M
local notation "F" => DGFunctor.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R G) (dgYoneda R G)
local notation "s" => dgGluingAxesRepresentableCofiberData R C D M zc hc zd hd X

/-- 元の下側二セルを対象宇宙だけ上げた実二単体。 -/
def dgGluingAxesCommonLowerCell : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R GG 2 :=
  (dgGluingAxesCofiberLowerCell R C D M zc hc zd hd X).simplex.map (U)

/-- 元の上側二セルを対象宇宙だけ上げた実二単体。 -/
def dgGluingAxesCommonUpperCell : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R GG 2 :=
  (dgGluingAxesCofiberUpperCell R C D M zc hc zd hd X).simplex.map (U)

/-- 共通宇宙の上下二セルは、元の同じ対角で厳密に一致する。 -/
lemma dgGluingAxesCommonCells_compatible :
    SSet.stdSimplex.δ (1 : Fin 3) ≫
      (SSet.yonedaEquiv.symm (dgGluingAxesCommonUpperCell R C D M zc hc zd hd X) :
        (Δ[2] : SSet.{max (u + 1) (max v w)}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R GG) =
    SSet.stdSimplex.δ (1 : Fin 3) ≫
      SSet.yonedaEquiv.symm (dgGluingAxesCommonLowerCell R C D M zc hc zd hd X) := by
  erw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply congrArg SSet.yonedaEquiv.symm
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R G).δ 1
      (dgGluingAxesCofiberUpperCell R C D M zc hc zd hd X).simplex =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R G).δ 1 (dgGluingAxesCofiberLowerCell R C D M zc hc zd hd X).simplex :=
    (dgGluingAxesCofiberUpperCell R C D M zc hc zd hd X).d₁.trans
      (dgGluingAxesCofiberLowerCell R C D M zc hc zd hd X).d₁.symm
  exact (dgSimplex_map_face _ (U) 1).trans
    ((congrArg (fun t => t.map (U)) h).trans (dgSimplex_map_face _ (U) 1).symm)

/-- 同じ共通宇宙の下側二セルの像は、元の実代表 cofiber の下側二セル。 -/
lemma dgGluingAxesCommonLowerCell_yoneda :
    (dgGluingAxesCommonLowerCell R C D M zc hc zd hd X).map (F) = (s).lowerTriangle :=
  (dgSimplex_commonUniverse_map _ (dgYoneda R G)).trans
    (dgGluingAxesCofiberLowerCell_yoneda R C D M zc hc zd hd X)

/-- 同じ共通宇宙の上側二セルの像は、元の実代表 cofiber の上側二セル。 -/
lemma dgGluingAxesCommonUpperCell_yoneda :
    (dgGluingAxesCommonUpperCell R C D M zc hc zd hd X).map (F) = (s).upperTriangle :=
  (dgSimplex_commonUniverse_map _ (dgYoneda R G)).trans
    (dgGluingAxesCofiberUpperCell_yoneda R C D M zc hc zd hd X)

end SerrePositivity.KST.SConstruction
