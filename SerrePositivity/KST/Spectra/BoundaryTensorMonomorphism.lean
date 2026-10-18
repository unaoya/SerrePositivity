module

public import SerrePositivity.KST.Spectra.SimplexTensorRelativeLatching
public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct

/-!
概要：境界をパラメーターとする標準単体の相対 latching 射の単射性。
方針：pushout-product を二つの部分複体の積の和として表す。
規約：通常の部分複体の包含と押し出しの同型だけを使う。
使われ方：Goerss–Jardine VII §4、VIII §1。Tot の境界に対する相対充填。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.SimplexTensorBoundary

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：同じ二辺を押し出した二つの pushout-product の arrow 同型。
方針：各押し出しを選択された押し出しへ同定する。
規約：終域の同型は恒等。
使われ方：Goerss–Jardine VII §4。部分複体の積の和との比較。 -/
def productSquareArrowIso {A B C D : SSet.{u}} {i : A ⟶ B} {j : C ⟶ D}
    (s t : (curriedTensor SSet.{u}).PushoutObjObj i j) :
    Arrow.mk s.ι ≅ Arrow.mk t.ι := by
  refine Arrow.isoMk (s.isPushout.isoPushout ≪≫ t.isPushout.isoPushout.symm) (Iso.refl _) ?_
  change (s.isPushout.isoPushout.hom ≫ t.isPushout.isoPushout.inv) ≫ t.ι = s.ι ≫ 𝟙 _
  rw [Category.comp_id]
  apply s.hom_ext
  · simp only [Category.assoc, IsPushout.inl_isoPushout_hom_assoc,
      IsPushout.inl_isoPushout_inv_assoc, Functor.PushoutObjObj.inl_ι]
  · simp only [Category.assoc, IsPushout.inr_isoPushout_hom_assoc,
      IsPushout.inr_isoPushout_inv_assoc, Functor.PushoutObjObj.inr_ι]

/-- 概要：二つの境界包含の pushout-product は単射。
方針：二つの部分複体の積の和の包含と同型にする。
規約：どちらの次数も零を許す。
使われ方：Goerss–Jardine VII §4。Tot の境界充填の単射条件。 -/
lemma boundaryProduct_mono (m n : ℕ) :
    Mono (boundaryProductSquare (SSet.boundary.{u} m).ι n).ι := by
  let t := SSet.Subcomplex.unionProd.pushoutObjObj (SSet.boundary.{u} n)
    (SSet.boundary.{u} m)
  exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff
    (productSquareArrowIso (boundaryProductSquare (SSet.boundary.{u} m).ι n) t)).mpr
    (inferInstanceAs (Mono ((SSet.boundary.{u} n).unionProd (SSet.boundary.{u} m)).ι))

/-- 概要：境界包含のパラメーターの射は標準単体図式上で Reedy 単射。
方針：相対 latching の pushout-product 表示で単射性を移す。
規約：各成分だけでなく相対 latching 射の単射性。
使われ方：Goerss–Jardine VII §4、VIII §1。Tot の acyclic な相対充填。 -/
lemma boundaryMap_reedy_mono (m : ℕ) :
    reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u})
      (map (SSet.boundary.{u} m).ι) := by
  intro j
  induction j using SimplexCategory.rec with | _ n =>
  exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff
    (relativeLatchingProductArrowIso (SSet.boundary.{u} m).ι n)).mpr
    (boundaryProduct_mono m n)

end

end SerrePositivity.KST.Spectra.SimplexTensorBoundary
