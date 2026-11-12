module
public import SerrePositivity.KST.Fibration.ZeroMiddleFixedHornUpperBoundary

/-!
概要：同じ三面を回収する制御充填族を、元の二胞体を端面とする全三角柱族へ渡す。
方針：同じ元のホーンへの制限式を各面と元の中間三角柱に前合成する。
規約：制御充填の存在は主張せず、既存充填との固定三面比較を保持する。
使われ方：K-6 c4 の Ind-S (9) の再構成供給後の全族照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
  (K : SSet.{u + 1}) (F : (Δ[3] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hF : ((horn 3 (2 : Fin 4)).ι ▷ K) ≫ F =
    fst (horn 3 (2 : Fin 4) : SSet.{u + 1}) K ≫ zeroMiddleFullSKanHorn s hZ)

include hF in
/-- 概要：同じホーンを回収する制御充填族は、元の族と全一単体で厳密一致する。
方針：三次元ホーンが全辺を含むことを同じ制限式に使う。
規約：全二胞体や指定全長 Hom の一致はここから推論しない。
使われ方：元の三角柱の各縦辺の同じ実射の回収。 -/
theorem zeroMiddleControlledFillerFamily_one (x : (Δ[3] ⊗ K) _⦋1⦌) :
    F.app (Opposite.op ⦋1⦌) x =
      (zeroMiddleFullSKanTetrahedron s hZ).app (Opposite.op ⦋1⦌) x.1 := by
  have hx : x.1 ∈ (horn 3 (2 : Fin 4)).obj (Opposite.op ⦋1⦌) := by
    rw [horn_obj_eq_univ (2 : Fin 4) 1]
    exact Set.mem_univ _
  have he := congrArg (fun G => G.app (Opposite.op ⦋1⦌) (⟨x.1, hx⟩, x.2)) hF
  change F.app (Opposite.op ⦋1⦌) x =
    (zeroMiddleFullSKanHorn s hZ).app (Opposite.op ⦋1⦌) ⟨x.1, hx⟩ at he
  rw [zeroMiddleFullSKanTetrahedron_horn] at he
  exact he

include hF in
/-- 概要：制御充填族の面 1 は元の指定 native 二胞体の全族そのもの。
方針：元のホーン内の面 1 に同じ制限式を前合成する。
規約：元の二胞体を任意の同境界の充填へ置き換えない。
使われ方：制御された三角柱族の終端の厳密回収。 -/
theorem zeroMiddleControlledFillerFamily_original :
    (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ F =
      fst (Δ[2] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
          (Opposite.op ⦋2⦌) s) := by
  have he := congrArg (fun G => (horn₃₂.ι₁ ▷ K) ≫ G) hF
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, horn.ι_ι,
    ← Category.assoc, whiskerRight_fst, Category.assoc,
    zeroMiddleFullSKanHorn_original] at he
  exact he

/-- 概要：構成済みの制御充填から元の二胞体へ戻る全三角柱族。
方針：元と同じ中間三角柱写像を全パラメータで前合成する。
規約：同じ制御充填 F を保持し、新しい充填を選ばない。
使われ方：指定全長 Hom の回収後の上側全族比較の実写像。 -/
def zeroMiddleControlledPrismFamily : ((Δ[2] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ K ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism ▷ K) ≫ F

/-- 概要：同じ三角柱族は制御された全上側二胞体から始まる。
方針：元の三角柱写像の始端の厳密式を使う。
規約：元の非指定充填の上側で代用しない。
使われ方：Ind-S (9) の指定上側との照合。 -/
theorem zeroMiddleControlledPrismFamily_zero :
    (SSet.ι₀ ▷ K) ≫ zeroMiddleControlledPrismFamily K F =
      (stdSimplex.δ (2 : Fin 4) ▷ K) ≫ F := by
  rw [zeroMiddleControlledPrismFamily, ← Category.assoc,
    ← MonoidalCategory.comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_zero]

include hF in
/-- 概要：同じ三角柱族は元の指定 native 二胞体の全族へ厳密に終わる。
方針：元の三角柱写像の終端と同じ制御充填の面 1 を回収する。
規約：境界だけでなく全二胞体を保持する。
使われ方：K-6 c4 の元の Verdier 上側への全族の戻し。 -/
theorem zeroMiddleControlledPrismFamily_one :
    (SSet.ι₁ ▷ K) ≫ zeroMiddleControlledPrismFamily K F =
      fst (Δ[2] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
          (Opposite.op ⦋2⦌) s) := by
  rw [zeroMiddleControlledPrismFamily, ← Category.assoc,
    ← MonoidalCategory.comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_one]
  exact zeroMiddleControlledFillerFamily_original s hZ K F hF

/-- 概要：同じ制御三角柱族は、その制御上側の共有対角を全時刻固定する。
方針：元の三角柱写像の対角固定式を全パラメータで使う。
規約：共有対角を同じ全単体写像として保持する。
使われ方：指定上下二胞体を動く共有対角で貼り合わせる前の制限回収。 -/
theorem zeroMiddleControlledPrismFamily_diagonal :
    ((stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ▷ K) ≫
      zeroMiddleControlledPrismFamily K F =
      (fst (Δ[1] : SSet.{u + 1}) Δ[1] ▷ K) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ (stdSimplex.δ (2 : Fin 4) ▷ K) ≫ F := by
  rw [zeroMiddleControlledPrismFamily, ← Category.assoc,
    ← MonoidalCategory.comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_diagonal]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]

end SerrePositivity.KST.Fibration
