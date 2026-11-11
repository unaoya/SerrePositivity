module
public import SerrePositivity.KST.Fibration.ClosedCofiberRawProjection
public import SerrePositivity.KST.Fibration.Relative.ClosedKernelFlags
public import SerrePositivity.KST.Fibration.KilledKernelIso
public import SerrePositivity.KST.Fibration.WeakCofiberRawProjection

/-!
概要：元の P 全旗の cofiber 係数を、同じ P 内の実係数へ厳密に戻す。
方針：零圏へ送る元の関手の核同型と、元の包含による相対完全射を使う。
規約：P を Verdier 商の核へ置換せず、零圏は P 内の全旗を表すためだけに使う。
使われ方：K-B2 向け初期評価四角形の元の cofiber 係数比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration
open Relative
variable {B : StableModel.{u}} (P : ClosedStablePredicate B)

/-- 概要：元の P 内の全旗の cofiber 係数は元の P と包含そのもので厳密同型。
方針：元の零圏への射に既存の零化核同型を適用する。
規約：P の retract 閉包を取らない。使われ方：全有限積係数の実同型。 -/
def closedFlagKernelCoefficientIso :
    closedStableModel (kernelClosedPredicate (closedKernelZeroMap P)) ≅ closedStableModel P :=
  killedKernelIso (closedKernelZeroMap P) (fun _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _)

/-- 概要：元の P 包含は同じ全 cofiber の相対入力条件を保つ。
方針：全 P 対象が元の P へ含まれるという実頂点回収を使う。
規約：商比較を仮定しない。使われ方：同じ補完の実後合成。 -/
def closedFlagKernelRelativeInputMap :
    weakRelativeInput (closedKernelZeroMap P) ⟶
      (⟨B, ClosedStablePredicate.top B, P⟩ : RelativeStableModel.{u}) :=
  ⟨sInputExactMap (closedKernelInclusion P),
    ⟨fun _ _ => trivial, fun x _ => closedSubcategory_vertex P x⟩⟩

/-- 概要：同じ相対入力射の cofiber 係数作用は元の係数包含同型。
方針：同じ完全な全部分圏制限を全単体で計算する。
規約：元の P 自身が行先。使われ方：係数射の全正反復局所化同型。 -/
theorem closedFlagKernelRelativeInputMap_right :
    relativeRightFunctor.map (closedFlagKernelRelativeInputMap P) =
      (closedFlagKernelCoefficientIso P).hom := Subtype.ext rfl

/-- 概要：元の P 全旗の共通 cofiber 補完を、同じ包含で実後合成する。
方針：元の相対入力射に正本の相対 cofiber 関手を適用する。
規約：同じ核・商 API を新設しない。使われ方：指定補完の全族比較。 -/
def closedFlagKernelCofiberPost :
    weakCofiberModel (closedKernelZeroMap P) ⟶
      relativeCofiberStableModel (ClosedStablePredicate.top B) P :=
  relativeCofiberMap (closedFlagKernelRelativeInputMap P)

/-- 概要：同じ包含で補完を写した cofiber は元の P 値係数へ厳密に戻る。
方針：正本の quotient 頂点の自然性と同じ係数同型の回収を使う。
規約：全入力族の厳密等式。使われ方：元の有限積の包含に沿う係数自然性。 -/
theorem closedFlagKernelCofiberPost_quotient :
    closedFlagKernelCofiberPost P ≫ relativeCofiberQuotient (ClosedStablePredicate.top B) P =
      relativeCofiberQuotient
        (ClosedStablePredicate.top (sInputModel (flagAmbient (closedStableModel P))))
        (kernelClosedPredicate (closedKernelZeroMap P)) ≫
          (closedFlagKernelCoefficientIso P).hom := by
  have h := relativeCofiberQuotient_naturality (closedFlagKernelRelativeInputMap P)
  rw [closedFlagKernelRelativeInputMap_right] at h
  exact h

/-- 概要：同じ補完の底辺後合成は元の P 包含による全矢印図式の後合成。
方針：正本の相対 cofiber 包含の自然性と元の cofiber 射影の自然性を合成する。
規約：同じ実底辺を全関手で保持。使われ方：二補完の充満忠実な比較。 -/
theorem closedFlagKernelCofiberPost_rawProjection :
    (closedFlagKernelCofiberPost P).val ≫ closedCofiberRawProjection P =
      weakCofiberRawProjection (closedKernelZeroMap P) ≫
        (ihom (Δ[1] : SSet.{u})).map (closedKernelInclusion P).hom := by
  have he : (closedFlagKernelCofiberPost P).val ≫
      (relativeCofiberInclusion (ClosedStablePredicate.top B) P).val =
      (relativeCofiberInclusion
        (ClosedStablePredicate.top (sInputModel (flagAmbient (closedStableModel P))))
        (kernelClosedPredicate (closedKernelZeroMap P))).val ≫
          cofiberPostcomp (closedKernelInclusion P).hom
            (sInputExactMap (closedKernelInclusion P)).property :=
    congrArg Subtype.val (relativeCofiberMap_inclusion (closedFlagKernelRelativeInputMap P))
  rw [closedCofiberRawProjection_inclusion, ← Category.assoc, he, Category.assoc]
  exact congrArg (fun f => (relativeCofiberInclusion
    (ClosedStablePredicate.top (sInputModel (flagAmbient (closedStableModel P))))
      (kernelClosedPredicate (closedKernelZeroMap P))).val ≫ f)
    (cofiberPostcomp_projection (closedKernelInclusion P).hom
      (sInputExactMap (closedKernelInclusion P)).property)

end SerrePositivity.KST.Fibration
