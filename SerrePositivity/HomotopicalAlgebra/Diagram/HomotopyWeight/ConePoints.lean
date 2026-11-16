module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorPiZero

/-!
# 実際の重み付き錐の零単体とその類

概要：Hovey §5.4 の重み付き錐の族から同じ錐空間の零単体を構成する。
方針：零単体をテンソルした重みの同型と錐の随伴、Yoneda 同型を合成する。
規約：元の重みと元の族を保持する。
使われ方：通常の錐の類と両 frame の錐比較の正規化。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory
open _root_.SerrePositivity.DiagramModel

variable (K : Type u) [SmallCategory K] (W : K ⥤ SSet.{u})

/-- 概要：重み付き錐の族は実際の錐空間の零単体（Hovey §5.4）。
方針：同じ零単体のテンソル同型を随伴と Yoneda に通す。
規約：零単体の型は元の coneSpace のもの。
使われ方：元の通常の錐の具体的な代表。 -/
def conePoint {F : K ⥤ SSet.{u}} (s : W ⟶ F) :
    ((WeightedCones.coneSpace K W).obj F).obj (Opposite.op (SimplexCategory.mk 0)) :=
  SSet.yonedaEquiv ((WeightedCones.adjunction K W).homEquiv _ F
    ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.zeroTensorWeightIso K W).hom ≫ s))

/-- 概要：重み付き錐の族の零単体の連結成分（Hovey §5.4）。
方針：同じ零単体を元の π₀ へ送る。
規約：別の錐空間への置換はしない。
使われ方：両側の frame で元の錐の類を追跡する。 -/
def coneClass {F : K ⥤ SSet.{u}} (s : W ⟶ F) :
    SSet.π₀ ((WeightedCones.coneSpace K W).obj F) := SSet.π₀.mk (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint K W s)

/-- 概要：錐の零単体は元の図式射による後合成に自然（Hovey §5.4）。
方針：同じ随伴の終域自然性を Yoneda 同型へ移す。
規約：図式全体に自然な族を後合成する。
使われ方：混合 Hom への二つの比較の零単体の照合。 -/
lemma conePoint_map {F G : K ⥤ SSet.{u}} (s : W ⟶ F) (f : F ⟶ G) :
    (((WeightedCones.coneSpace K W).map f).app (Opposite.op (SimplexCategory.mk 0)))
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint K W s) = _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint K W (s ≫ f) := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint, ← SSet.yonedaEquiv_comp]
  have h := (WeightedCones.adjunction K W).homEquiv_naturality_right
    ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.zeroTensorWeightIso K W).hom ≫ s) f
  exact congrArg SSet.yonedaEquiv ((by simpa only [Category.assoc] using h.symm))

/-- 概要：錐の類は元の図式射の同じ後合成で写る（Hovey §5.4）。
方針：零単体の自然性を π₀ へ送る。
規約：元の coneSpace の誘導する写像を使う。
使われ方：両 frame の共同比較のクラス計算。 -/
lemma coneClass_map {F G : K ⥤ SSet.{u}} (s : W ⟶ F) (f : F ⟶ G) :
    SSet.mapπ₀ ((WeightedCones.coneSpace K W).map f) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K W s) =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K W (s ≫ f) := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass, SSet.mapπ₀_mk, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint_map]
  rfl

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
