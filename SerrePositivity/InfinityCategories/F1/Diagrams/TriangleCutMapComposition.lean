module

public import SerrePositivity.InfinityCategories.F1.Coherent.PathCutRightEndpoint

/-!
概要：同じ側の対象を通る合成を、標準単体への切断座標の射として計算する。
方針：既存の path ごとの最大元の合成則を全旗に適用する。
規約：全次数の射の等式を供給する。
使われ方：二切断による長 Hom 置換の単位側の合成則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma controlledTriangleCutMap_comp_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 0) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ pathCutLastZeroMap t hi k =
      snd _ _ ≫ pathCutLastZeroMap t hj k := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply stdSimplex.ext
  intro l
  exact pathCutLastZero_comp_zero t hi hj (P.obj l) (Q.obj l)

lemma controlledTriangleCutMap_comp_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ pathCutLastZeroMap t hi k =
      fst _ _ ≫ pathCutLastZeroMap t hi j := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply stdSimplex.ext
  intro l
  exact pathCutLastZero_comp_one t hi hj (P.obj l) (Q.obj l)

end SerrePositivity.InfinityCategories
