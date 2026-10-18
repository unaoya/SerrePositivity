module

public import SerrePositivity.KST.Spectra.SimplexTensorBoundary
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
概要：標準単体とパラメーターの射の相対 latching 射の pushout-product 表示。
方針：境界の表示同型で押し出しを比較し、horn と単射の積の anodyne 性を移す。
規約：モデル圏構造は使わず、実際の押し出しの arrow 同型を与える。
使われ方：Goerss–Jardine VII §4、HTT A.3.3。通常の Tot の Reedy horn 充填。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.KST.Spectra.SimplexTensorBoundary

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B : SSet.{u}} (f : A ⟶ B) (n : ℕ)

/-- 概要：境界包含とパラメーターの射の実際の pushout-product の正方形。
方針：相対 latching の押し出しと同じ順序の二辺を選ぶ。
規約：pushout-product の左右の包含だけを逆順に表示する。
使われ方：Goerss–Jardine VII §4。Tot の horn の相対境界。 -/
def boundaryProductSquare : (curriedTensor SSet.{u}).PushoutObjObj
    (SSet.boundary.{u} n).ι f where
  pt := pushout ((SSet.boundary.{u} n).toSSet ◁ f) ((SSet.boundary.{u} n).ι ▷ A)
  inl := pushout.inr _ _
  inr := pushout.inl _ _
  isPushout := (IsPushout.of_hasPushout
    ((SSet.boundary.{u} n).toSSet ◁ f) ((SSet.boundary.{u} n).ι ▷ A)).flip

/-- 概要：境界表示の相対押し出しから pushout-product への比較。
方針：境界の表示同型の自然性と包含の公式で押し出しの射を作る。
規約：押し出しの二つの対象でともに同型。
使われ方：HTT A.3.3。相対 latching の arrow 同型の始域。 -/
abbrev relativeProductMap :=
  pushout.map
    (HomPresentation.tensorSourceMap (SubcomplexTensor.diagram (SSet.boundary.{u} n)) (map f))
    (SubcomplexTensor.inclusion (SSet.boundary.{u} n) (diagram A))
    ((SSet.boundary.{u} n).toSSet ◁ f) ((SSet.boundary.{u} n).ι ▷ A)
    (iso B n).hom (𝟙 _) (iso A n).hom (iso_natural f n)
    ((Category.comp_id _).trans (iso_inclusion A n).symm)

instance relativeProductMap_isIso : IsIso (relativeProductMap f n) := by
  exact pushout.map_isIso _ _ _ _ (iso B n).hom (𝟙 _) (iso A n).hom _ _

/-- 概要：境界 tensor の相対射は実際の pushout-product と同型。
方針：押し出しの二つの包含の後で可換性を検証する。
規約：終域の同型は恒等同型。
使われ方：Goerss–Jardine VII §4。anodyne 性の移送。 -/
def relativeTensorProductArrowIso :
    Arrow.mk (relativeBoundaryTensorMap (map f) n) ≅
      Arrow.mk (boundaryProductSquare f n).ι := by
  refine Arrow.isoMk (asIso (relativeProductMap f n)) (Iso.refl _) ?_
  change relativeProductMap f n ≫ (boundaryProductSquare f n).ι =
    relativeBoundaryTensorMap (map f) n ≫ 𝟙 _
  rw [Category.comp_id]
  apply pushout.hom_ext
  · rw [← Category.assoc, pushout.inl_desc, Category.assoc]
    change (iso B n).hom ≫ (boundaryProductSquare f n).inr ≫ _ = _
    rw [Functor.PushoutObjObj.inr_ι]
    change (iso B n).hom ≫ ((SSet.boundary.{u} n).ι ▷ B) = _
    rw [iso_inclusion]
    exact (HomPresentation.inl_relativeTensorMap _ (map f) _).symm
  · rw [← Category.assoc, pushout.inr_desc, Category.id_comp]
    change (boundaryProductSquare f n).inl ≫ _ = _
    rw [Functor.PushoutObjObj.inl_ι]
    exact (HomPresentation.inr_relativeTensorMap
      (SubcomplexTensor.diagram (SSet.boundary.{u} n)) (map f)
      (SubcomplexTensor.simplexCocone (SSet.boundary.{u} n))).symm

/-- 概要：標準単体とパラメーターの射の相対 latching 射は pushout-product。
方針：相対境界 tensor との一般の同型を合成する。
規約：次数 n の相対 latching 射を実際の arrow 圏で比較する。
使われ方：Goerss–Jardine VII §4、HTT A.3.3。Tot の充填の主計算。 -/
def relativeLatchingProductArrowIso :
    Arrow.mk (relativeLatchingMap simplex (SimplexCategory.mk n) (map f)) ≅
      Arrow.mk (boundaryProductSquare f n).ι :=
  (relativeBoundaryTensorArrowIso (map f) n).symm ≪≫ relativeTensorProductArrowIso f n

/-- 概要：anodyne なパラメーターの射は標準単体図式上で Reedy anodyne。
方針：境界包含が単射なので pushout-product の anodyne 性を使う。
規約：Kan 性やモデル圏の弱同値類は仮定しない。
使われ方：Goerss–Jardine VII §4。Tot の全ての horn の充填。 -/
lemma map_reedy_anodyne (hf : SSet.anodyneExtensions f) :
    reedyLeft simplex SSet.anodyneExtensions (map f) := by
  intro j
  induction j using SimplexCategory.rec with | _ k =>
  exact (SSet.anodyneExtensions.arrow_iso_iff (relativeLatchingProductArrowIso f k)).mpr
    (SSet.anodyneExtensions_pushoutObjObjι (boundaryProductSquare f k) hf)

end

end SerrePositivity.KST.Spectra.SimplexTensorBoundary
