module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction
public import Mathlib.CategoryTheory.Adhesive.PushoutProduct

/-!
# すべての単射に対する右持ち上げ性を持つ射の切断上で固定された強い収縮を構成する

## 概要
すべての単射に対する右持ち上げ性を持つ射の切断上で固定された強い収縮を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。

## 規約と注意
射pのすべての単射に対する右持ち上げ性を使い、基底と指定部分上の比較を保持する。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0453][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0453
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative homotopies over a fixed map and strong section contractions

All-monomorphism right lifting retains both endpoints, the entire prescribed
subobject homotopy, and the entire projected interval. No model structure is used.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.MonoRightLiftingRelativeHomotopy
variable {E B : SSet.{v}} (p : E ⟶ B)
  (hp : (MorphismProperty.monomorphisms SSet.{v}).rlp p)

include hp in
lemma exists_vertical_homotopy {Y : SSet.{v}} (f g : Y ⟶ E)
    (hfg : f ≫ p = g ≫ p) :
    ∃ H : SSet.Homotopy f g,
      H.h ≫ p = fst Y (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ f ≫ p := by
  let b := LargeParameterHomotopy.boundaryMap f g
  let q := fst Y (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ f ≫ p
  have hw : b ≫ p = Y ◁ (SSet.boundary 1).ι ≫ q := by
    apply (LargeParameterHomotopy.boundaryColimit Y).hom_ext
    rintro ⟨j⟩
    cases j
    · change (Y ◁ SSet.boundary.ι (1 : Fin 2)) ≫ (b ≫ p) =
        (Y ◁ SSet.boundary.ι (1 : Fin 2)) ≫ (Y ◁ (SSet.boundary 1).ι ≫ q)
      dsimp only [b, q]
      rw [← Category.assoc, LargeParameterHomotopy.boundaryMap_zero]
      conv_rhs => rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
        SSet.stdSimplex.δ_one_eq_const]
      rfl
    · change (Y ◁ SSet.boundary.ι (0 : Fin 2)) ≫ (b ≫ p) =
        (Y ◁ SSet.boundary.ι (0 : Fin 2)) ≫ (Y ◁ (SSet.boundary 1).ι ≫ q)
      dsimp only [b, q]
      rw [← Category.assoc, LargeParameterHomotopy.boundaryMap_one, Category.assoc, ← hfg]
      conv_rhs => rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
        SSet.stdSimplex.δ_zero_eq_const]
      rfl
  have : HasLiftingProperty (Y ◁ (SSet.boundary 1).ι) p := hp _ inferInstance
  let sq : CommSq b (Y ◁ (SSet.boundary 1).ι) p q := ⟨hw⟩
  refine ⟨{ h := sq.lift, h₀ := ?_, h₁ := ?_, rel := ?_ }, sq.fac_right⟩
  · change SSet.ι₀ ≫ sq.lift = f
    rw [← LargeParameterHomotopy.section_zero Y, Category.assoc,
      ← SSet.boundary.ι_ι (1 : Fin 2), whiskerLeft_comp, Category.assoc, sq.fac_left]
    dsimp only [b]
    rw [LargeParameterHomotopy.boundaryMap_zero]
    rfl
  · change SSet.ι₁ ≫ sq.lift = g
    rw [← LargeParameterHomotopy.section_one Y, Category.assoc,
      ← SSet.boundary.ι_ι (0 : Fin 2), whiskerLeft_comp, Category.assoc, sq.fac_left]
    dsimp only [b]
    rw [LargeParameterHomotopy.boundaryMap_one]
    rfl
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)


include hp in
lemma exists_extension {X Y : SSet.{v}} (i : X ⟶ Y) [Mono i]
    {f g : Y ⟶ E} (H : SSet.Homotopy f g)
    (A : SSet.Homotopy (i ≫ f) (i ≫ g))
    (ha : A.h ≫ p = i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h ≫ p) :
    ∃ V : SSet.Homotopy f g,
      V.h ≫ p = H.h ≫ p ∧
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = A.h := by
  let pp := KanRelativeLifting.boundaryProduct i
  have : Mono (Arrow.mk i).hom := inferInstanceAs (Mono i)
  have : Mono (Arrow.mk (SSet.boundary 1).ι).hom :=
    inferInstanceAs (Mono (SSet.boundary 1).ι)
  have : Mono pp.ι :=
    CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.instMonoHomObjArrowFunctorPushoutProduct
      (X := Arrow.mk i) (Y := Arrow.mk (SSet.boundary 1).ι)
  have : HasLiftingProperty pp.ι p := hp _ inferInstance
  let b := pp.isPushout.desc (LargeParameterHomotopy.boundaryMap f g) A.h
    (KanHomotopyExtension.boundary_compatibility i f g A)
  have hw : b ≫ p = pp.ι ≫ (H.h ≫ p) := by
    apply pp.isPushout.hom_ext
    · dsimp only [b]
      rw [← Category.assoc, pp.isPushout.inl_desc, ← Category.assoc, pp.inl_ι]
      rw [← HomotopyEndpointComparison.boundary_eq H, Category.assoc]
      rfl
    · dsimp only [b]
      rw [← Category.assoc, pp.isPushout.inr_desc, ← Category.assoc, pp.inr_ι]
      exact ha
  let sq : CommSq b pp.ι p (H.h ≫ p) := ⟨hw⟩
  have hb : Y ◁ (SSet.boundary 1).ι ≫ sq.lift =
      LargeParameterHomotopy.boundaryMap f g := by
    rw [show Y ◁ (SSet.boundary 1).ι = pp.inl ≫ pp.ι from pp.inl_ι.symm,
      Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  have hA : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ sq.lift = A.h := by
    rw [show i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) = pp.inr ≫ pp.ι from
      pp.inr_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inr_desc _ _ _
  refine ⟨{ h := sq.lift, h₀ := ?_, h₁ := ?_, rel := ?_ }, sq.fac_right, hA⟩
  · change SSet.ι₀ ≫ sq.lift = f
    rw [← LargeParameterHomotopy.section_zero Y, Category.assoc,
      ← SSet.boundary.ι_ι (1 : Fin 2), whiskerLeft_comp, Category.assoc, hb,
      LargeParameterHomotopy.boundaryMap_zero]
    rfl
  · change SSet.ι₁ ≫ sq.lift = g
    rw [← LargeParameterHomotopy.section_one Y, Category.assoc,
      ← SSet.boundary.ι_ι (0 : Fin 2), whiskerLeft_comp, Category.assoc, hb,
      LargeParameterHomotopy.boundaryMap_one]
    rfl
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

include hp in
lemma exists_relative_vertical_homotopy {X Y : SSet.{v}} (i : X ⟶ Y) [Mono i]
    (f g : Y ⟶ E) (hfg : f ≫ p = g ≫ p) (hi : i ≫ f = i ≫ g) :
    ∃ H : SSet.Homotopy f g,
      H.h ≫ p = fst Y (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ f ≫ p ∧
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h =
        fst X (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ i ≫ f := by
  obtain ⟨H, hH⟩ := exists_vertical_homotopy p hp f g hfg
  let A : SSet.Homotopy (i ≫ f) (i ≫ g) := {
    h := fst X (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ i ≫ f
    h₀ := by ext n x; rfl
    h₁ := by rw [← hi]; ext n x; rfl
    rel := by
      apply NatTrans.ext
      funext n
      exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property) }
  obtain ⟨V, hV, hrel⟩ := exists_extension p hp i H A (by
    change (fst X _ ≫ i ≫ f) ≫ p = i ▷ _ ≫ H.h ≫ p
    rw [hH, whiskerRight_fst_assoc, Category.assoc, Category.assoc])
  exact ⟨V, hV.trans hH, hrel⟩

include hp in
/-- すべての単射に対する右持ち上げ性を持つ射の切断上で固定された強い収縮を構成する。

射pのすべての単射に対する右持ち上げ性を使い、基底と指定部分上の比較を保持する。
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。
-/
lemma exists_strong_contraction (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) :
    ∃ H : SSet.Homotopy (𝟙 E) (p ≫ s),
      H.h ≫ p = fst E (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ p ∧
      s ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h =
        fst B (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ s := by
  have : IsSplitMono s := IsSplitMono.mk' ⟨p, hs⟩
  obtain ⟨H, hH⟩ := MonoRightLiftingContraction.exists_vertical_contraction p hp s hs
  let A : SSet.Homotopy (s ≫ 𝟙 E) (s ≫ (p ≫ s)) := {
    h := fst B (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ s
    h₀ := by ext n x; rfl
    h₁ := by
      change SSet.ι₁ ≫ _ = s ≫ (p ≫ s)
      rw [← Category.assoc s p s, hs, Category.id_comp]
      ext n x
      rfl
    rel := by
      apply NatTrans.ext
      funext n
      exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property) }
  have hA : A.h = fst B (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ s := rfl
  obtain ⟨V, hV, hrel⟩ := exists_extension p hp s H A (by
    rw [hA, hH, whiskerRight_fst_assoc, Category.assoc])
  exact ⟨V, hV.trans hH, hrel.trans hA⟩

end SerrePositivity.SimplicialModel.MonoRightLiftingRelativeHomotopy
