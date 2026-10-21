module

public import SerrePositivity.InfinityCategories.F1.HomSpanSectionTransport

/-!
概要：元の span の恒等始域での因子比較を、同じ両端評価の比較として正規化する。
方針：既存の指定同型の端点の恒等合成だけを除去する。
規約：元の切断・単位・因子比較の値を保持する。
使われ方：底制限の輸送正方形の指定境界を明示する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の span の切断輸送は、同じ共通 Hom 上で元の二射影を結ぶ。 -/
def homSpanSectionBoundaryIso {P X Y : SSet.{u}}
    [Quasicategory P] [Quasicategory X] [Quasicategory Y]
    (p : P ⟶ X) (q : P ⟶ Y) (s : X ⟶ P) (hp : IsFullyFaithful p)
    (hs : s ≫ p = 𝟙 X) : FunctorIso (p ≫ (s ≫ q)) q :=
  F2.functorIsoOfEq (homSpanSectionTransportFactorIso p q s hp hs (𝟙 P))
    (by rw [Category.id_comp]) (Category.id_comp q)

end SerrePositivity.InfinityCategories
