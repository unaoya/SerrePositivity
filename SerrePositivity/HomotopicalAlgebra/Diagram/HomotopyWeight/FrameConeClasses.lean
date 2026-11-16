module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConePoints

/-!
# 実現の普通の射が与える錐の類の正規化

概要：Hovey §5.4 の重み付き実現の随伴から作った錐の類は元の局所化射。
方針：同じ標準 frame の零次同型と二つの随伴の自然性を使う。
規約：実現対象と元の射をそのまま保持する。
使われ方：通常の錐から具体的な計算対象への射のクラス計算。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.DiagramModel

variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u, u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u}) (B : K ⥤ SimplexCategory ⥤ C)

omit [ModelCategory C] in
/-- 概要：随伴で作った錐の零単体は同じ零次同型による Hom の像（Hovey §5.4）。
方針：テンソル実現の合成随伴と実現随伴の始域自然性を使う。
規約：同じ零単体テンソル同型を使う。
使われ方：錐の π₀ 比較の元の射での正規化。 -/
lemma tensorFrameHomIso_point {Y : C}
    (f : (FrameWeightRealization.functor K B).obj W ⟶ Y) :
    ((((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso K W B).app Y).hom).app (Opposite.op (SimplexCategory.mk 0)))
        ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameZeroIso K W B).hom ≫ f) =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint Kᵒᵖ W ((FrameWeightRealization.adjunction K B).homEquiv W Y f) := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorRealizationAdjunction K W B).homEquiv _ Y (_ ≫ f)) =
    SSet.yonedaEquiv ((WeightedCones.adjunction Kᵒᵖ W).homEquiv _ _
      ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.zeroTensorWeightIso Kᵒᵖ W).hom ≫
        (FrameWeightRealization.adjunction K B).homEquiv W Y f))
  simp only [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorRealizationAdjunction, Adjunction.comp_homEquiv]
  exact congrArg (fun h => SSet.yonedaEquiv
    ((WeightedCones.adjunction Kᵒᵖ W).homEquiv _ _ h))
      ((FrameWeightRealization.adjunction K B).homEquiv_naturality_left _ f)

variable (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries Kᵒᵖ).rlp.llp (initial.to W))
  (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (g : n ⟶ m),
    weakEquivalences C ((B.obj k).map g))
  {D : Type w} [Category.{t} D] (Q : C ⥤ D) [Q.IsLocalization (weakEquivalences C)]

/-- 概要：実現の射からの錐の類は元の射の局所化像（Hovey §5.4）。
方針：同じ零単体の計算と frame の零次同型の順逆の相殺を使う。
規約：元の実現対象からの射に対する厳密な式。
使われ方：通常の錐からの比較射の正規化。 -/
lemma frameConePiZeroLocalizationEquiv_class {Y : C} [IsFibrant Y]
    (f : (FrameWeightRealization.functor K B).obj W ⟶ Y) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv K W B hW hB hconst Q Y
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖ W ((FrameWeightRealization.adjunction K B).homEquiv W Y f)) = Q.map f := by
  have hp : SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso K W B).app Y).hom
      (SSet.π₀.mk ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameZeroIso K W B).hom ≫ f)) =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖ W ((FrameWeightRealization.adjunction K B).homEquiv W Y f) := by
    rw [SSet.mapπ₀_mk]
    exact congrArg SSet.π₀.mk (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso_point K W B f)
  rw [← hp, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv_mk, ← Q.map_comp, Iso.inv_hom_id_assoc]

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
