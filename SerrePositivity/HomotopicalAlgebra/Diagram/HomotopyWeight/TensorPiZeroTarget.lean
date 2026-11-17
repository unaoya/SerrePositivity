module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorPiZero

/-!
# 重み付き錐の π₀ 比較の終域自然性

概要：Hovey §5.4 の重み付き実現からの局所化 Hom 比較は終域の射に自然。
方針：同じ標準 frame の零単体の代表と Hom 同型の自然性を使う。
規約：モデル構造は元の値圏だけに置く。
使われ方：反対圏の右 frame から元の始域自然性を得る。
-/

@[expose] public section

noncomputable section

universe u v w t

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.DiagramModel

variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u, u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u}) (B : K ⥤ SimplexCategory ⥤ C)
  (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries Kᵒᵖ).rlp.llp (initial.to W))
  (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((B.obj k).map f))
  {D : Type w} [Category.{t} D] (Q : C ⥤ D) [Q.IsLocalization (weakEquivalences C)]

/-- 概要：重み付き錐の π₀ は元の終域の後合成に自然（Hovey §5.4）。
方針：零単体を同じ frame Hom の同型で表示し、元の射の後合成を計算する。
規約：両終域は fibrant、別の対象へ置換しない。
使われ方：右 frame の試験始域の射と局所化 Hom の照合。 -/
lemma frameConePiZeroLocalizationEquiv_target {Y Z : C} [IsFibrant Y] [IsFibrant Z]
    (f : Y ⟶ Z) (z : SSet.π₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone K W B).obj Y)) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv K W B hW hB hconst Q Z
        (SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone K W B).map f) z) =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv K W B hW hB hconst Q Y z ≫ Q.map f := by
  let e := (SSet.π₀Functor.mapIso ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso K W B).app Y)).toEquiv
  obtain ⟨z, rfl⟩ := e.surjective z
  induction z using SSet.π₀.rec with | mk g =>
  change _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv K W B hW hB hconst Q Z
      (SSet.mapπ₀ _ (SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso K W B).app Y).hom (SSet.π₀.mk g))) =
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv K W B hW hB hconst Q Y
      (SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso K W B).app Y).hom (SSet.π₀.mk g)) ≫ Q.map f
  have hn : ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso K W B).app Y).hom ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone K W B).map f =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame K W B)).map f ≫ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso K W B).app Z).hom :=
    ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso K W B).hom.naturality f).symm
  rw [← SSet.mapπ₀_comp_apply, hn, SSet.mapπ₀_comp_apply, SSet.mapπ₀_mk,
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv_mk, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv_mk]
  change Q.map (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameZeroIso K W B).inv ≫ Q.map (g ≫ f) = _
  rw [Q.map_comp, Category.assoc]

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
