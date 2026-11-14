module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.Site.FlatTopologyPushout
public import Mathlib.CategoryTheory.Sites.Coverage

/-!
# Prism の平坦位相と構造前層の層条件

## 概要
完全忠実平坦な単一射の被覆で平坦位相を生成し、構造前層の層条件を等化子に帰着する。

## 方針
被覆の底変換に完備押し出しを用いる。環の元ごとの等化子から、環射の貼り合わせを得る。

## 規約
BS 著者版 Corollary 3.12 (a), (c)。site は環側の圏の反対圏。

## 使われ方
構造環とその prism イデアルによる剰余環の Čech 降下。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PrismOver

open CategoryTheory CategoryTheory.Limits Opposite

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}

/-- 完全忠実平坦な単一射による被覆。 -/
def flatCoverage (hκ : IsAdmissibleCutoff P R κ) : Coverage (PrismOver P R κ)ᵒᵖ where
  coverings X := {S | ∃ (Y : PrismOver P R κ) (f : X.unop ⟶ Y),
    IsFaithfullyFlat f ∧ S = Presieve.singleton f.op}
  pullback := by
    intro X X' g S hS
    obtain ⟨Y, f, hf, rfl⟩ := hS
    obtain ⟨Y', f', g', h, hf'⟩ := exists_isPushout_isFaithfullyFlat hκ f hf g.unop
    refine ⟨Presieve.singleton f'.op, ⟨Y', f', hf', rfl⟩, ?_⟩
    intro Z j hj
    cases hj
    refine ⟨op Y, g'.op, f.op, Presieve.singleton_self _, ?_⟩
    simpa only [op_comp, Quiver.Hom.op_unop] using congrArg Quiver.Hom.op h.w

/-- 単一射の平坦な被覆で生成する Grothendieck 位相。 -/
def flatTopology (hκ : IsAdmissibleCutoff P R κ) : GrothendieckTopology (PrismOver P R κ)ᵒᵖ :=
  (flatCoverage hκ).toGrothendieck

/-- 環側で台の環を取る構造関手。 -/
@[expose] def structureRing : PrismOver P R κ ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of X.B
  map f := CommRingCat.ofHom f.toHom.toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 環側で prism イデアルによる剰余環を取る構造関手。 -/
@[expose] def quotientStructureRing : PrismOver P R κ ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of (X.B ⧸ X.Q.ideal)
  map f := CommRingCat.ofHom f.toHom.quotientMap
  map_id X := by
    apply CommRingCat.hom_ext
    exact OrientedPrism.Hom.quotientMap_id X.Q
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact OrientedPrism.Hom.quotientMap_comp g.toHom f.toHom

/-- 概要：各平坦被覆で台の元に関する等化子条件を満たす環の前層は層。
方針：任意の環からの射を、値ごとに一意に貼り合わせる。
規約：BS 著者版 Corollary 3.12 (c) の通常の層条件。
使われ方：構造環とその剰余環に、完備 Čech の次数 0 と 1 の完全性を適用する。 -/
theorem isSheaf_of_flatEqualizer (hκ : IsAdmissibleCutoff P R κ)
    (F : PrismOver P R κ ⥤ CommRingCat.{u})
    (hF : ∀ ⦃X Y : PrismOver P R κ⦄ (f : X ⟶ Y), IsFaithfullyFlat f →
      ∃ (Z : PrismOver P R κ) (i j : Y ⟶ Z), f ≫ i = f ≫ j ∧
        Function.Injective (F.map f).hom ∧
        ∀ b : F.obj Y, (F.map i).hom b = (F.map j).hom b →
          ∃ a : F.obj X, (F.map f).hom a = b) :
    Presheaf.IsSheaf (flatTopology hκ) (unopUnop _ ⋙ F) := by
  intro E
  apply (Presieve.isSheaf_coverage (flatCoverage hκ) _).mpr
  intro X S hS
  obtain ⟨Y, f, hf, rfl⟩ := hS
  obtain ⟨Z, i, j, hw, hi, hex⟩ := hF f hf
  rw [Presieve.isSheafFor_singleton]
  intro x hx
  have hcompat : x ≫ F.map i = x ≫ F.map j := by
    apply hx i.op j.op
    simpa only [op_comp] using congrArg Quiver.Hom.op hw
  have hpoint (t : E) : ∃ a : F.obj X.unop, (F.map f).hom a = x.hom t := by
    apply hex
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom hcompat) t
  choose a ha using hpoint
  let y : E →+* F.obj X.unop :=
    { toFun := a
      map_zero' := hi (by rw [ha, map_zero, map_zero])
      map_one' := hi (by rw [ha, map_one, map_one])
      map_add' s t := hi (by simp only [map_add, ha])
      map_mul' s t := hi (by simp only [map_mul, ha]) }
  refine ⟨CommRingCat.ofHom y, ?_, ?_⟩
  · change CommRingCat.ofHom y ≫ F.map f = x
    apply CommRingCat.hom_ext
    exact RingHom.ext ha
  · intro z hz
    change z ≫ F.map f = x at hz
    apply CommRingCat.hom_ext
    ext t
    apply hi
    exact (RingHom.congr_fun (congrArg CommRingCat.Hom.hom hz) t).trans (ha t).symm

end SerrePositivity.BhattScholze.Prismatic.PrismOver

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Cor 3.12" (partial := special) "固定基底 (A,(d)) 上・濃度 cutoff の site（D22）。(a) 完全平坦な押し出し、構造環と d 剰余の全次数の Čech 完全性と層条件（BS-W15 K4）。∞ 層・RΓ への接続は drafts ／ 11-11 更新（2） ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver.flatTopology
attribute [cite BS19 "Def 4.1" (partial := special) "affine・向き付き・濃度 ≤ κ の site と平坦位相、構造層が層であること（BS-W15 K4）。RΓ_Δ（Čech–Alexander による計算）は G10 待ち ／ 11-11 更新（2）"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver.flatTopology
