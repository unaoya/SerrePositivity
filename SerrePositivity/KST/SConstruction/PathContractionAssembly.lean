module
public import SerrePositivity.KST.SConstruction.SimplicialPathContraction
public import SerrePositivity.KST.SConstruction.SPathBoundary
public import SerrePositivity.KST.SConstruction.DiagonalAssembly

/-! # 経路収縮の零行への制限と元の区間組み立て
概要：経路空間の既存の収縮を零行へ制限して境界に写すと、元の一次段の区間組み立てになる。
方針：後続頂点の包含、収縮の cut、零行への退化の合成を区間の各単体で計算する。
規約：区間の向きを保持する。使われ方：元の構造射の随伴と fiber 比較のホモトピーの照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 零行からの退化と経路収縮を境界へ制限すると、区間単体の元の順序写像になる。 -/
lemma simplicialPathCut_zeroRow_boundary (d : SimplexCategory)
    (t : (Δ[1] : SSet.{u}).obj (Opposite.op d)) :
    simplicialPathTail d ≫ simplicialPathCut d t ≫
      SimplexPrefix.functor.map (SimplexCategory.const d ⦋0⦌ 0) = stdSimplex.objEquiv t := by
  ext j : 3
  change Fin.cases (0 : Fin 2) (fun _ => 1)
      (Fin.cases (0 : Fin (d.len + 2)) (SimplexPrefix.cut d t).toOrderHom
        ((0 : Fin (d.len + 2)).succAbove j)) = (stdSimplex.objEquiv t).toOrderHom j
  rw [Fin.succAbove_zero_apply]
  change Fin.cases (0 : Fin 2) (fun _ => 1)
    (if (stdSimplex.objEquiv t).toOrderHom j = 0 then 0 else j.succ) =
      (stdSimplex.objEquiv t).toOrderHom j
  split_ifs with h
  · exact h.symm
  · change (1 : Fin 2) = (stdSimplex.objEquiv t).toOrderHom j
    have hn (a : Fin 2) (ha : a ≠ 0) : (1 : Fin 2) = a := by fin_cases a <;> simp_all
    exact hn _ h

/-- 経路の元の収縮の零行への制限を境界へ写すと、元の区間組み立てに厳密に一致する。 -/
lemma simplicialPathDiagonalCylinder_zeroRow_boundary (D : SimplicialObject SSet.{u}) :
    (diagonalZeroColumn (simplicialPath D) ▷ (Δ[1] : SSet.{u})) ≫
        simplicialPathDiagonalCylinder D ≫ simplicialDiagonalFunctor.map
          (simplicialPathBoundary D) =
      (β_ (D.obj (Opposite.op ⦋1⦌)) (Δ[1] : SSet.{u})).hom ≫ diagonalAssembly 1 D := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  change ((D.map (SimplexPrefix.functor.map (SimplexCategory.const d.unop ⦋0⦌ 0)).op ≫
    D.map (simplicialPathCut d.unop z.2).op ≫
      D.map (simplicialPathTail d.unop).op).app d) z.1 =
        (D.map (stdSimplex.objEquiv z.2).op).app d z.1
  rw [← D.map_comp, ← D.map_comp, ← op_comp, ← op_comp, Category.assoc,
    simplicialPathCut_zeroRow_boundary]
  rfl

end SerrePositivity.KST.SConstruction
