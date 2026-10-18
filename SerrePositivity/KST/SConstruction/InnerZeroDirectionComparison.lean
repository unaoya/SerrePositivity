module
public import SerrePositivity.KST.SConstruction.InnerZeroDirectionCoordinates

/-! # 最内側の零方向の自己関手の比較
概要：零次数を持つ内側の S と、最後の零方向の自己関手を自然に比較する。
方針：座標の自然同型と添字の等号を合成し、零方向の包含との可換性を示す。
規約：安定な入力について自然。使われ方：全零境界への包含。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open scoped Simplicial

/-- 概要：最内側の S_0 の合成を最後の零方向の自己関手へ移す同型。
方針：可変の内側の座標比較と零次数の添字の一致を合成する。
規約：外側の全次数は n。使われ方：定数部分の境界への包含。 -/
def innerZeroDirectionComparisonIso (r n : ℕ) :
    sEndofunctor.{u} 0 ⋙ (multiSEndofunctor r).obj (fun _ => Opposite.op ⦋n⦌) ≅
      (multiSEndofunctor (r + 1)).obj
        ((zeroDirectionsIndex {Fin.last r}).obj (fun _ => Opposite.op ⦋n⦌)) :=
  innerVariableSComparisonIso r (fun _ => Opposite.op ⦋n⦌) (Opposite.op ⦋0⦌) ≪≫
    (multiSEndofunctor (r + 1)).mapIso
      (eqToIso (innerVariableIndex_obj_zero r (Opposite.op ⦋n⦌)))

/-- 概要：対角次数で可変の内側の S を全方向の反復へ移す同型。
方針：可変の内側の座標比較と対角添字の一致を合成する。
規約：安定な入力について自然。使われ方：零方向の包含の比較の終域。 -/
def innerDiagonalComparisonIso (r n : ℕ) :
    sEndofunctor.{u} n ⋙ (multiSEndofunctor r).obj (fun _ => Opposite.op ⦋n⦌) ≅
      (multiSEndofunctor (r + 1)).obj (fun _ => Opposite.op ⦋n⦌) :=
  innerVariableSComparisonIso r (fun _ => Opposite.op ⦋n⦌) (Opposite.op ⦋n⦌) ≪≫
    (multiSEndofunctor (r + 1)).mapIso
      (eqToIso (innerVariableIndex_obj_diagonal r (Opposite.op ⦋n⦌)))

/-- 概要：内側の零次数からの作用と最後の零方向の包含は座標比較の下で可換。
方針：内側の自然性に、零方向の添字の作用素の厳密な一致を合成する。
規約：自己関手の自然変換の等号。使われ方：商への降下の可換図式。 -/
lemma innerZeroDirectionComparisonIso_inclusion (r n : ℕ) :
    Functor.whiskerRight
        (simplicialStableEndofunctor.{u}.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op)
        ((multiSEndofunctor r).obj (fun _ => Opposite.op ⦋n⦌)) ≫
      (innerDiagonalComparisonIso r n).hom =
        (innerZeroDirectionComparisonIso r n).hom ≫
          (multiSEndofunctor (r + 1)).map
            ((zeroDirectionsIndexNat {Fin.last r}).app (fun _ => Opposite.op ⦋n⦌)) := by
  let d := Opposite.op ⦋n⦌
  let f := (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
  let D := multiSEndofunctor.{u} (r + 1)
  have hz : (innerVariableIndex r (fun _ => d)).map f ≫
        eqToHom (innerVariableIndex_obj_diagonal r d) =
      eqToHom (innerVariableIndex_obj_zero r d) ≫
        (zeroDirectionsIndexNat {Fin.last r}).app (fun _ => d) := by
    rw [← innerVariableIndex_zero_map]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rfl
  change _ ≫ ((innerVariableSComparisonIso r (fun _ => d) d).hom ≫
      D.map (eqToHom (innerVariableIndex_obj_diagonal r d))) =
    ((innerVariableSComparisonIso r (fun _ => d) (Opposite.op ⦋0⦌)).hom ≫
      D.map (eqToHom (innerVariableIndex_obj_zero r d))) ≫ _
  rw [← Category.assoc, innerVariableSComparisonIso_naturality, Category.assoc,
    ← CategoryTheory.Functor.map_comp, hz, CategoryTheory.Functor.map_comp, Category.assoc]

end SerrePositivity.KST.SConstruction
