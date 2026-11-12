module
public import SerrePositivity.KST.Fibration.ZeroMiddleFactorizationComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledFactorizationTetrahedronFamily

/-!
概要：Ind-S (9b) の実供給を、同じ元の零中間二胞体の因子分解と全族比較へ代入する。
方針：公開された controlledFactorizationTetraFamily を元の供給命題へ接続する。
規約：(9b) の存在仮定は不要。(9) の正規化再構成とは分離し、元の三面・全 Hom を保持する。
使われ方：K-6 c4 の実制御充填と既存充填の固定三面比較。
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

/-- 概要：採用済み (9b) の供給命題は Ind-S の実構成で満たされる。
方針：元の三面と full native Hom の同じ型へ公開定理を直接適用する。
規約：命題の緩和・コピー・新しい存在仮定は行わない。
使われ方：既存の条件付き因子分解利用側から (9b) の仮定を外す。 -/
theorem zeroMiddleFactorizationTetraSupply_of_indS9b : zeroMiddleFactorizationTetraSupply.{u} :=
  fun X₀ X₁ X₂ X₃ f g h K T hfirst hlast =>
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledFactorizationTetraFamily X₀ X₁ X₂ X₃ f g h K T hfirst hlast

variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
  (K : SSet.{u + 1})

/-- 概要：元の native 二胞体を厳密保持する、実供給済みの因子分解三単体族。
方針：同じ元の零中間データを Ind-S (9b) の供給へ代入する。
規約：元の三面・長 Hom を保持し、存在仮定を取らない。
使われ方：元の実ホーンを回収する制御充填。 -/
def zeroMiddleNativeFactorizationTetra :=
  zeroMiddleFactorizationTetra s hZ K zeroMiddleFactorizationTetraSupply_of_indS9b

/-- 概要：同じ実供給族は元の三面のホーン全体を厳密回収する。
方針：実供給を既存のホーン回収定理へ代入する。
規約：元の三面から別の充填へ選び直さない。
使われ方：同じ実固定三面 fiber 内の比較に入る。 -/
theorem zeroMiddleNativeFactorizationTetra_horn :
    ((horn 3 (2 : Fin 4)).ι ▷ K) ≫ zeroMiddleNativeFactorizationTetra s hZ K =
      fst (horn 3 (2 : Fin 4) : SSet.{u + 1}) K ≫ zeroMiddleFullSKanHorn s hZ :=
  zeroMiddleFactorizationTetra_horn s hZ K zeroMiddleFactorizationTetraSupply_of_indS9b

/-- 概要：実供給の制御上側は元の指定二胞体の全 native Hom を回収する。
方針：(9b) の実証明を同じ full Hom の読出しへ代入する。
規約：合成端・一つの辺だけの一致へ弱めない。
使われ方：元の全 S• Hom の core 制限との照合。 -/
theorem zeroMiddleNativeFactorizationTetra_longHom (k : K _⦋0⦌) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 4)
      (SSet.yonedaEquiv (lift (𝟙 (Δ[3] : SSet.{u + 1})) (SSet.const k) ≫
        zeroMiddleNativeFactorizationTetra s hZ K))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) s).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) :=
  zeroMiddleFactorizationTetra_longHom s hZ K zeroMiddleFactorizationTetraSupply_of_indS9b k

/-- 概要：同じ実供給上側は元の既存上側と固定三面比較を経て全族同型。
方針：供給された同じ実充填を固定ホーン内比較へ渡す。
規約：元の非指定充填も保持する。(9) の再構成は使わない。
使われ方：制御上側と元の上側の比較の実入口。 -/
def zeroMiddleNativeFactorizationUpperIso :=
  zeroMiddleFactorizationUpperIso s hZ K zeroMiddleFactorizationTetraSupply_of_indS9b

/-- 概要：同じ実供給上側は元の native 二胞体全族へ実三角柱で戻る。
方針：同じ充填の実三角柱を既存の可逆比較へ渡す。
規約：元の全二胞体と共有対角を保持する。
使われ方：K-6 c4 の指定上側の実全族比較。 -/
def zeroMiddleNativeFactorizationPrismIso :=
  zeroMiddleFactorizationPrismIso s hZ K zeroMiddleFactorizationTetraSupply_of_indS9b

end SerrePositivity.KST.Fibration
