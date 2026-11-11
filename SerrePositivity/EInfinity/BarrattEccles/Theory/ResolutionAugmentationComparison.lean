module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# 指定された増大保存射の鎖ホモトピー逆

## 概要
HA 3.2.4.7 の二色比較で、同じ対象の射影解像度間の指定射を鎖ホモトピー同値にする。

## 方針
逆射は恒等射の持ち上げで作り、両合成と恒等射を `liftHomotopy` で比較する。

## 規約
指定された順方向の比較射を変更しない。表現のアーベル圏でも同じ構成を使える。

## 使われ方
Σ_m × Σ_n の表現の圏で二色の比較の増大と射影性を証明した後、同変な逆を作る。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity
open CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C] {T : C}

/-- HA 3.2.4.7 の二色比較に使う、指定射を保つ射影解像度間のホモトピー同値。 -/
def resolutionHomotopyEquivOfAugmentation (P Q : ProjectiveResolution T)
    (f : P.complex ⟶ Q.complex) (hf : f ≫ Q.π = P.π) :
    HomotopyEquiv P.complex Q.complex := by
  let g := ProjectiveResolution.lift (𝟙 T) Q P
  have hg : g ≫ P.π = Q.π := by
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using
      (ProjectiveResolution.lift_commutes (𝟙 T) Q P)
  refine { hom := f, inv := g, homotopyHomInvId := ?_, homotopyInvHomId := ?_ }
  · apply ProjectiveResolution.liftHomotopy (P := P) (Q := P) (𝟙 T)
    · rw [Category.assoc, hg, hf, CategoryTheory.Functor.map_id, Category.comp_id]
    · simp
  · apply ProjectiveResolution.liftHomotopy (P := Q) (Q := Q) (𝟙 T)
    · rw [Category.assoc, hf, hg, CategoryTheory.Functor.map_id, Category.comp_id]
    · simp

/-- 二色比較の順方向は元の指定射そのものである（HA 3.2.4.7）。 -/
@[simp]
lemma resolutionHomotopyEquivOfAugmentation_hom (P Q : ProjectiveResolution T)
    (f : P.complex ⟶ Q.complex) (hf : f ≫ Q.π = P.π) :
    (resolutionHomotopyEquivOfAugmentation P Q f hf).hom = f := rfl

end SerrePositivity.EInfinity
