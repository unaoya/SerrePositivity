module
public import SerrePositivity.KST.SConstruction.PathContractionAssembly

/-! # 経路収縮による元の定数経路切断の固定
概要：既存の経路収縮は区間全体で元の定数経路を厳密に固定する。
方針：cut と零段への唯一の写像の合成を計算する。
規約：元の切断の全高次単体を保つ。使われ方：元の点つき経路商への収縮の降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 元の収縮は定数経路の切断を区間全体で厳密に固定する。 -/
lemma simplicialPathDiagonalCylinder_section (D : SimplicialObject SSet.{u}) :
    (simplicialPathDiagonalSection D ▷ (Δ[1] : SSet.{u})) ≫
      simplicialPathDiagonalCylinder D =
        fst (D.obj (Opposite.op ⦋0⦌)) (Δ[1] : SSet.{u}) ≫ simplicialPathDiagonalSection D := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  change ((D.map (SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d.unop)).op ≫
    D.map (simplicialPathCut d.unop z.2).op).app d) z.1 =
      (D.map (SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d.unop)).op).app d z.1
  rw [← D.map_comp, ← op_comp]
  have h : simplicialPathCut d.unop z.2 ≫
      SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d.unop) =
      SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d.unop) :=
    Subsingleton.elim _ _
  rw [h]

end SerrePositivity.KST.SConstruction
