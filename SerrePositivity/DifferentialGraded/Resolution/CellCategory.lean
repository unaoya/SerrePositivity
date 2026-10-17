module
public import SerrePositivity.DifferentialGraded.Resolution.CellAssociativity
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectCategory
public import SerrePositivity.DifferentialGraded.Resolution.Basic

/-! # 任意の小さいdg圏のK-flat解像度の構成

## 概要
初期cycle coverから全境界cellの付加を反復した極限。
元のHomのflatness、有界性、モデル構造又は比較定理の引用を仮定しない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

namespace DGCategoryCellResolution

def candidate : FixedObjectAugmentation A D D id where
  category := ofHomObjects A D (candidateHom A D) (candidateUnit A D) (candidateComposition A D)
    (candidateComposition_left_unit A D) (candidateComposition_right_unit A D)
    (fun a b c d => by rw [candidateComposition_assoc, Iso.inv_hom_id_assoc])
  map := candidateAugmentation A D
  map_id := candidateUnit_augmentation A D
  map_comp := candidateComposition_augmentation A D

abbrev Source : Type v := (candidate A D).Objects

def augmentation : DGFunctor A (Source A D) D := (candidate A D).augmentation

lemma source_homKFlat : localHomKFlat A (Source A D) :=
  (candidate A D).objects_homKFlat (candidateHom_kFlat A D)

lemma augmentation_homQuasiIso : HomQuasiIso (augmentation A D) :=
  fun x y => candidateAugmentation_quasiIso A D x.val y.val

lemma augmentation_essSurj : (augmentation A D).onHomotopy.EssSurj where
  mem_essImage Y := by
    let x : Source A D := ⟨ForgetEnrichment.to (C := D) (Complex A) Y.as⟩
    exact ⟨(toHomotopy A (Source A D)).obj (ForgetEnrichment.of (Complex A) x), ⟨Iso.refl _⟩⟩

lemma augmentation_quasiEquivalence : QuasiEquivalence (augmentation A D) :=
  ⟨augmentation_homQuasiIso A D, augmentation_essSurj A D⟩

def resolution : KFlatDGResolution.{u, v, v} A D where
  source := Source A D
  augmentation := augmentation A D
  quasiEquivalence := augmentation_quasiEquivalence A D
  homKFlat := source_homKFlat A D

end DGCategoryCellResolution

namespace KFlatDGResolution

/-- 全境界cell付加の逐次余極限による標準の指定K-flat dg圏解像度。 -/
def canonical : KFlatDGResolution.{u, v, v} A D := DGCategoryCellResolution.resolution A D

/-- 任意可換環上の任意の小さい非有界dg圏は、小さいK-flat dg圏解像度を持つ。 -/
theorem nonempty : Nonempty (KFlatDGResolution.{u, v, v} A D) := ⟨canonical A D⟩

end KFlatDGResolution
end SerrePositivity.DifferentialGraded
