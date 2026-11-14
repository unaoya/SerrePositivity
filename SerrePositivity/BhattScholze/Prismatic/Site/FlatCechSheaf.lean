module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.Site.FlatCechConerve
public import SerrePositivity.BhattScholze.Prismatic.Site.FlatSiteSheaf
public import SerrePositivity.HomologicalAlgebra.Cech.Basic
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# 完備 Čech 完全性から構造前層の層条件へ

## 概要
増大 Čech 複体が次数零と一で完全なら、平坦被覆について環の等化子条件が成り立つ。

## 方針
Čech の単体次数零にある一脚の押し出しと元の被覆先を比較する。次数零から一への
交代余面微分の核を、二つの余面の等化子として読む。

## 規約
BS 著者版 Corollary 3.12 (c) の通常の環値の層条件。

## 使われ方
構造前層とその prism イデアルによる剰余前層。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PrismOver

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}

/-- 増大した完備 Čech 余脈体に環値関手を適用する。 -/
@[expose] def flatRingCech (hκ : IsAdmissibleCutoff P R κ)
    (F : PrismOver P R κ ⥤ CommRingCat.{u}) {X Y : PrismOver P R κ}
    (f : X ⟶ Y) (hf : IsFaithfullyFlat f) : CosimplicialObject.Augmented CommRingCat.{u} :=
  (CosimplicialObject.Augmented.whiskeringObj _ _ F).obj (flatAugmentedCechConerve hκ f hf)

/-- 概要：平坦被覆ごとの増大 Čech 完全性から環値の層条件を得る。
方針：最初の二つの微分から単射性と二つの余面の等化子条件を取り出す。
規約：BS 著者版 Corollary 3.12 (c)。全次数の完全性を与えて適用できる。
使われ方：有限剰余の逆極限で得た完全性を、構造前層とその剰余の層条件に移す。 -/
theorem isSheaf_of_flatRingCechExact (hκ : IsAdmissibleCutoff P R κ)
    (F : PrismOver P R κ ⥤ CommRingCat.{u})
    (hex : ∀ ⦃X Y : PrismOver P R κ⦄ (f : X ⟶ Y) (hf : IsFaithfullyFlat f),
      Cech.AugmentedRingCechExact (flatRingCech hκ F f hf)) :
    Presheaf.IsSheaf (flatTopology hκ) (unopUnop _ ⋙ F) := by
  apply isSheaf_of_flatEqualizer hκ F
  intro X Y f hf
  let S := flatAugmentedCechConerve hκ f hf
  let U := flatRingCech hκ F f hf
  letI := hasWidePushout_flat hκ f hf (0 + 1)
  let ι : Y ⟶ S.right.obj ⦋0⦌ := WidePushout.ι (fun _ : Fin (0 + 1) ↦ f) 0
  let r : S.right.obj ⦋0⦌ ⟶ Y := WidePushout.desc (arrows := fun _ : Fin (0 + 1) ↦ f) f (fun _ ↦ 𝟙 Y) (fun _ ↦ Category.comp_id f)
  have hι : ι ≫ r = 𝟙 Y := WidePushout.ι_desc (fun _ : Fin (0 + 1) ↦ f) _ _ _ 0
  have hε : f ≫ ι = S.hom.app ⦋0⦌ :=
    WidePushout.arrow_ι (fun _ : Fin (0 + 1) ↦ f) 0
  let i : Y ⟶ S.right.obj ⦋1⦌ := ι ≫ S.right.δ (0 : Fin 2)
  let j : Y ⟶ S.right.obj ⦋1⦌ := ι ≫ S.right.δ (1 : Fin 2)
  have hw (k : Fin 2) : (f ≫ ι) ≫ S.right.δ k = S.hom.app ⦋1⦌ := by
    rw [hε]
    have h := (S.hom.naturality (SimplexCategory.δ k)).symm
    change S.hom.app ⦋0⦌ ≫ S.right.δ k = 𝟙 _ ≫ S.hom.app ⦋1⦌ at h
    simpa only [Category.id_comp] using h
  have hsq : f ≫ i = f ≫ j := by
    change f ≫ (ι ≫ S.right.δ (0 : Fin 2)) = f ≫ (ι ≫ S.right.δ (1 : Fin 2))
    rw [← Category.assoc, ← Category.assoc, hw, hw]
  have he : F.map f ≫ F.map ι = U.hom.app ⦋0⦌ := by
    rw [← F.map_comp, hε]
    rfl
  have hsplit : Function.Injective (F.map ι).hom := by
    have h := congrArg F.map hι
    rw [F.map_comp, F.map_id] at h
    intro x y hxy
    have hleft (b : F.obj Y) : (F.map r).hom ((F.map ι).hom b) = b :=
      RingHom.congr_fun (congrArg CommRingCat.Hom.hom h) b
    exact (hleft x).symm.trans ((congrArg (F.map r).hom hxy).trans (hleft y))
  obtain ⟨hinj, hexact, _⟩ := hex f hf
  refine ⟨S.right.obj ⦋1⦌, i, j, hsq, ?_, ?_⟩
  · intro a b hab
    apply hinj
    rw [← he]
    exact congrArg (F.map ι).hom hab
  · intro b hb
    let b' := (F.map ι).hom b
    have hi (k : Fin 2) : (U.right.δ k).hom b' =
        (F.map (ι ≫ S.right.δ k)).hom b := by
      rw [F.map_comp]
      rfl
    let K := (alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (U.right ⋙ Cech.ringToAb)
    have hb' : K.d 0 1 b' = 0 := by
      change (AlternatingCofaceMapComplex.objD (U.right ⋙ Cech.ringToAb) 0) b' = 0
      change (∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) • CosimplicialObject.δ (U.right ⋙ Cech.ringToAb) k) b' = 0
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
        AddCommGrpCat.hom_add_apply]
      change (U.right.δ (0 : Fin 2)).hom b' + -(U.right.δ (1 : Fin 2)).hom b' = 0
      rw [hi, hi]
      exact add_neg_eq_zero.mpr hb
    obtain ⟨a, ha⟩ := (hexact b').mp hb'
    refine ⟨a, hsplit ?_⟩
    change (F.map f ≫ F.map ι).hom a = b'
    rw [he]
    exact ha

end SerrePositivity.BhattScholze.Prismatic.PrismOver

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Cor 3.12" (partial := special) "固定基底 (A,(d)) 上・濃度 cutoff の site（D22）。(a) 完全平坦な押し出し、構造環と d 剰余の全次数の Čech 完全性と層条件（BS-W15 K4）。∞ 層・RΓ への接続は drafts ／ 11-11 更新（2） ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver.isSheaf_of_flatRingCechExact
attribute [cite BS19 "Def 4.1" (partial := special) "affine・向き付き・濃度 ≤ κ の site と平坦位相、構造層が層であること（BS-W15 K4）。RΓ_Δ（Čech–Alexander による計算）は G10 待ち ／ 11-11 更新（2）"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver.isSheaf_of_flatRingCechExact
