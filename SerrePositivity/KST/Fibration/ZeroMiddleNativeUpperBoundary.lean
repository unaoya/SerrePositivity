module
public import SerrePositivity.KST.Fibration.ZeroMiddleNativeFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TetrahedronFamilyVertices

/-!
概要：実供給済み因子分解三単体族の制御上側を、元の二短辺へ厳密に戻す。
方針：同じ固定三面の回収と二つの単体恒等式で、欠面の両短辺を読む。
規約：同じ実 (9b) 充填を保持し、既存の非指定充填へ選び直さない。
使われ方：K-6 c4 の再構成上側の有限端点と制御充填の境界照合。
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
  (K : SSet.{u + 1})

/-- 概要：同じ実因子分解族の指定欠面を制御上側全族として読む。
方針：同じ供給済み三単体族の面二へ制限する。
規約：新たな充填を選ばない。使われ方：元の二短辺と全 native Hom の同時照合。 -/
def zeroMiddleNativeUpperFamily : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (stdSimplex.δ (2 : Fin 4) ▷ K) ≫ zeroMiddleNativeFactorizationTetra s hZ K

/-- 概要：同じ実供給の面三は元の厳密な第一因子分解二胞体。
方針：同じ元の実三面条件を回収する。
規約：全パラメータ固定。使われ方：欠面の第一短辺を読む。 -/
theorem zeroMiddleNativeFactorizationTetra_first :
    (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ zeroMiddleNativeFactorizationTetra s hZ K =
      fst (Δ[2] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm (zeroMiddleFullSKanFirstTriangle s hZ).simplex :=
  (zeroMiddleFactorizationTetra_spec s hZ K zeroMiddleFactorizationTetraSupply_of_indS9b).2.2.1

/-- 概要：同じ実供給の面零は元の厳密な第二合成二胞体。
方針：同じ元の実三面条件を回収する。
規約：全パラメータ固定。使われ方：欠面の第二短辺を読む。 -/
theorem zeroMiddleNativeFactorizationTetra_last :
    (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ zeroMiddleNativeFactorizationTetra s hZ K =
      fst (Δ[2] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm (zeroMiddleFullSKanLastTriangle s hZ).simplex :=
  (zeroMiddleFactorizationTetra_spec s hZ K zeroMiddleFactorizationTetraSupply_of_indS9b).1

/-- 概要：同じ制御上側全族の第一短辺は元の実 core 包含の定値全族。
方針：欠面の第一短辺を固定面三へ移し、元の厳密合成二胞体の第一辺を回収する。
規約：元の coherent な全一単体。使われ方：再構成上側始端の同じ第一境界。 -/
theorem zeroMiddleNativeUpperFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ zeroMiddleNativeUpperFamily s hZ K =
      fst (Δ[1] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
          (show stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩) ⟶
            fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩) from
              _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map
                (coreSFullRealizationInclusion (s.obj ⟨ULift.up 0⟩)))).edge := by
  have hid : (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u + 1}) ⟶ Δ[2]) ≫
      stdSimplex.δ (2 : Fin 4) = stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) :=
    (stdSimplex.δ_comp_δ (by decide : (2 : Fin 3) ≤ 2)).symm
  unfold zeroMiddleNativeUpperFamily
  rw [← Category.assoc, ← comp_whiskerRight, hid, comp_whiskerRight,
    Category.assoc, zeroMiddleNativeFactorizationTetra_first,
    ← Category.assoc, whiskerRight_fst, Category.assoc]
  exact congrArg (fun f => fst (Δ[1] : SSet.{u + 1}) K ≫ f)
    (zeroMiddleFullSKanFirstTriangle s hZ).δ_two_yonedaEquiv_symm

/-- 概要：同じ制御上側全族の第二短辺は元の全 S• 合成実射の定値全族。
方針：欠面の第二短辺を固定面零の長辺へ移し、元の厳密合成端を回収する。
規約：同じ実合成完全射。使われ方：再構成上側始端の同じ第二境界。 -/
theorem zeroMiddleNativeUpperFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ zeroMiddleNativeUpperFamily s hZ K =
      fst (Δ[1] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (zeroMiddleFullSKanComposite s hZ)).edge := by
  have hid : (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u + 1}) ⟶ Δ[2]) ≫
      stdSimplex.δ (2 : Fin 4) = stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) := by
    apply SSet.yonedaEquiv.injective
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  unfold zeroMiddleNativeUpperFamily
  rw [← Category.assoc, ← comp_whiskerRight, hid, comp_whiskerRight,
    Category.assoc, zeroMiddleNativeFactorizationTetra_last,
    ← Category.assoc, whiskerRight_fst, Category.assoc]
  exact congrArg (fun f => fst (Δ[1] : SSet.{u + 1}) K ≫ f)
    ((zeroMiddleFullSKanLastTriangle s hZ).δ_one_yonedaEquiv_symm.trans
      (congrArg (fun f => SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
        (zeroMiddleFullSKanComparison_last s hZ)))

/-- 概要：同じ制御上側の各入力の全 native Hom は元の指定二胞体のもの。
方針：同じ欠面とパラメータ評価を交換し、実 (9b) の native 回収を消費する。
規約：二短辺と同じ実充填を保持。使われ方：再構成上側端点との全長 Hom 照合。 -/
theorem zeroMiddleNativeUpperFamily_native (k : K _⦋0⦌) :
    HEq ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (zeroMiddleNativeUpperFamily s hZ K) k)).map
        ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) s).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) := by
  have he : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (zeroMiddleNativeUpperFamily s hZ K) k) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 4)
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (zeroMiddleNativeFactorizationTetra s hZ K) k)) := by
    apply SSet.yonedaEquiv.symm.injective
    rw [Equiv.symm_apply_apply, ← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp _ _ _
  rw [he]
  exact zeroMiddleNativeFactorizationTetra_longHom s hZ K k

end SerrePositivity.KST.Fibration
