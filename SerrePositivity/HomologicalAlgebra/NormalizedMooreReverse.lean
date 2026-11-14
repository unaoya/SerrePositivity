module
public import SerrePositivity.HomologicalAlgebra.AlternatingFaceReverse
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
概要：単体順序反転の Moore 正規化を元の正規化へ結ぶ指定鎖ホモトピー同値。
方針：Moore 包含、交代面複体の符号同型、指定正規化射影を合成する。
規約：自然性は全単体的対象の射に関して成り立ち、単なる次数ごとの同値でない。
使われ方：HA 1.2.4、G10 の反転豊穣 Hom と BK 重みの照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type*} [Category* C] [Abelian C]

/-- 指定包含・符号・射影から得る、反転正規化の鎖ホモトピー同値。 -/
def normalizedMooreReverseHomotopyEquiv (W : SimplicialObject C) :
    HomotopyEquiv ((normalizedMooreComplex C).obj (SimplicialObject.opFunctor.obj W))
      ((normalizedMooreComplex C).obj W) :=
  (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := SimplicialObject.opFunctor.obj W)).trans
      ((HomotopyEquiv.ofIso (alternatingFaceReverseIso W)).trans
        (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (Y := W)).symm)

/-- 全射に自然な、反転した正規化から元の正規化への指定射。 -/
def normalizedMooreReverse :
    SimplicialObject.opFunctor (C := C) ⋙ normalizedMooreComplex C ⟶
      normalizedMooreComplex C :=
  Functor.whiskerLeft SimplicialObject.opFunctor (inclusionOfMooreComplex C) ≫
    alternatingFaceReverseNatIso.hom ≫
    { app := DoldKan.PInftyToNormalizedMooreComplex
      naturality _ _ f := DoldKan.PInftyToNormalizedMooreComplex_naturality f }

/-- 鎖ホモトピー同値の前向き射は指定自然変換の成分そのもの。 -/
theorem normalizedMooreReverseHomotopyEquiv_hom (W : SimplicialObject C) :
    (normalizedMooreReverseHomotopyEquiv W).hom = normalizedMooreReverse.app W := rfl

end SerrePositivity.HomologicalAlgebra
