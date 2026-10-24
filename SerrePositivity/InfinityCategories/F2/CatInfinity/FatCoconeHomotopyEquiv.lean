module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.FatCoconeFromHomotopy
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaFiberFamilies

/-!
概要：太い余錐と動く定値図式への指定自然変換の厳密な全単射。
方針：座標の交換と fat join の貼り合わせの両逆を計算する。
規約：任意のパラメータと図式、充填性の仮定なし。
使われ方：対角 comma の族と太い coslice の族の同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：円柱の並べ替えとその逆の合成は恒等射。
方針：直積の座標で計算する。
規約：全パラメータを保持する。使われ方：自然変換側の往復則。 -/
lemma diagonalCoconeReorder_unreorder (K A : SSet.{u}) :
    diagonalCoconeReorder K A ≫ diagonalCoconeUnreorder K A = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：円柱の逆の並べ替えと元の合成も恒等射。
方針：直積の座標で計算する。
規約：時間を反転しない。使われ方：太い余錐側の往復則。 -/
lemma diagonalCoconeUnreorder_reorder (K A : SSet.{u}) :
    diagonalCoconeUnreorder K A ≫ diagonalCoconeReorder K A = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：太い余錐の自然変換と頂点から貼り直すと元の余錐に戻る。
方針：円柱・左端・右端で比較する。
規約：左図式の固定条件も保持する。使われ方：全単射の左逆則。 -/
lemma fatCoconeFromHomotopy_homotopy {A K C : SSet.{u}} {p : K ⟶ C}
    (F : fatJoin K A ⟶ C) (hF : fatJoinInl K A ≫ F = p) :
    fatCoconeFromHomotopy p (fatJoinInr K A ≫ F) (fatCoconeHomotopy F hF) = F := by
  apply fatJoin_hom_ext
  · rw [fatCoconeFromHomotopy_cylinder]
    change diagonalCoconeUnreorder K A ≫
      uncurry (curry (diagonalCoconeReorder K A ≫ fatJoinCylinder K A ≫ F)) = _
    rw [uncurry_curry, ← Category.assoc, diagonalCoconeUnreorder_reorder, Category.id_comp]
  · rw [fatCoconeFromHomotopy_fixed, hF]
  · exact fatCoconeFromHomotopy_apex _ _ _

/-- 概要：指定自然変換から貼り直した余錐の自然変換は元の射と一致する。
方針：円柱の評価と curry の往復則を使う。
規約：ホモトピー類だけでなく元の射の等式。使われ方：全単射の右逆則。 -/
lemma fatCoconeHomotopy_from_h {A K C : SSet.{u}} (p : K ⟶ C) (b : A ⟶ C)
    (H : SSet.Homotopy (SSet.const (functorVertex p)) (b ≫ constantDiagram K C)) :
    (fatCoconeHomotopy (fatCoconeFromHomotopy p b H)
      (fatCoconeFromHomotopy_fixed p b H)).h = H.h := by
  change curry (diagonalCoconeReorder K A ≫ fatJoinCylinder K A ≫
    fatCoconeFromHomotopy p b H) = H.h
  rw [fatCoconeFromHomotopy_cylinder]
  apply uncurry_injective
  rw [uncurry_curry, ← Category.assoc, diagonalCoconeReorder_unreorder, Category.id_comp]

/-- 概要：固定図式の太い余錐と定値図式への自然変換のデータは全単射。
方針：二つの構成の両逆を、依存する頂点と自然変換の組で確認する。
規約：パラメータも頂点族も任意。使われ方：対角 comma の正確な表示。 -/
def fatCoconeHomotopyEquiv {K C : SSet.{u}} (p : K ⟶ C) (A : SSet.{u}) :
    {F : fatJoin K A ⟶ C // fatJoinInl K A ≫ F = p} ≃
      Σ b : A ⟶ C, SSet.Homotopy (SSet.const (functorVertex p))
        (b ≫ constantDiagram K C) where
  toFun F := ⟨fatJoinInr K A ≫ F.val, fatCoconeHomotopy F.val F.property⟩
  invFun d := ⟨fatCoconeFromHomotopy p d.1 d.2, fatCoconeFromHomotopy_fixed p d.1 d.2⟩
  left_inv F := Subtype.ext (fatCoconeFromHomotopy_homotopy F.val F.property)
  right_inv d := unitCommaFiberDiagram_ext (constantDiagram K C) (functorVertex p)
    (fatCoconeFromHomotopy_apex p d.1 d.2) _ _ (fatCoconeHomotopy_from_h p d.1 d.2)

end SerrePositivity.InfinityCategories.F2
