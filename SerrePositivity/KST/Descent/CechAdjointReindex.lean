module

public import SerrePositivity.KST.Descent.CechReindexLocalization

/-!
# 左随伴な添字変更と実際のホモトピー極限

## 概要
左随伴な添字関手への制限が、実際のホモトピー極限を局所化後に自然同定することを証明する。

## 方針
添字随伴を点ごとの局所化へ移し、定数関手との指定同型と導来定数随伴の一意性を使う。

## 規約
左右の導来比較は相関した実際のデータから構成する。通常の極限の保存は使わない。

## 使われ方
論文 補題 3.2 の分裂余単体対象の降下と細分。τ 位相の層論を Čech 計算で置換する準備。
-/

@[expose] public section

noncomputable section

universe u vD uD vE uE vH uH

open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent.CechReindex

variable (K : Type u) [SmallCategory K] [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{u})]
  {D : Type uD} [Category.{vD} D] {H : Type uH} [Category.{vH} H]
  (Λ : SSet.{u} ⥤ H) [Λ.IsLocalization (weakEquivalences SSet.{u})]
  (QK : (K ⥤ SSet.{u}) ⥤ D)
  [QK.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{u}))]

/-- 概要：実際のホモトピー極限の相関した導来データ（補題 3.2）。
方針：指定 cofibrant 重みと左右の total derived 比較を同時に構成する。
規約：随伴と計算で同じ比較を使う。使われ方：添字変更の自然同型の正規化。 -/
abbrev homotopyData :=
  CofibrantCechWeight.derivedData K I J (HomotopyCones.weight K I J)
    (HomotopyCones.weight_isCofibrant K I J) Λ QK

/-- 概要：同じ導来データから定数随伴を構成（補題 3.2）。
方針：指定重みの可縮性と実際の導来随伴を使う。
規約：随伴を独立に選ばない。使われ方：左右の添字における実際の計算の比較。 -/
def homotopyAdjunction
    (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _) :
    HomotopyLimit.localizedConstant K Λ QK ⊣ (homotopyData K I J Λ QK).rightFunctor :=
  CofibrantCechWeight.DerivedData.constantAdjunction K I J (HomotopyCones.weight K I J)
    (HomotopyCones.weight_isCofibrant K I J) (HomotopyCones.weightComparison K I J)
    (HomotopyCones.weightComparison_objectwiseWeakEquivalence K I J) hcof Λ QK
    (HomotopyLimit.localizedConstant K Λ QK) (HomotopyLimit.constantComparison K Λ QK)
    (homotopyData K I J Λ QK)

/-- 概要：同じ導来データによる実際のホモトピー極限の計算（補題 3.2）。
方針：指定右比較を fibrant 置換で評価する。
規約：上の随伴と同じ右比較を使う。使われ方：実際の空間の計算との接続。 -/
def homotopyComputationIso :
    HomotopyCones.functor K I J ⋙ Λ ≅ QK ⋙ (homotopyData K I J Λ QK).rightFunctor :=
  CofibrantCechWeight.DerivedData.computationIso K I J (HomotopyCones.weight K I J)
    (HomotopyCones.weight_isCofibrant K I J) Λ QK (homotopyData K I J Λ QK)

variable (L : Type u) [SmallCategory L]
  {E : Type uE} [Category.{vE} E]
  (QL : (L ⥤ SSet.{u}) ⥤ E)
  [QL.IsLocalization (Projective.objectwise L (weakEquivalences SSet.{u}))]

/-- 概要：添字の左随伴への制限後の計算も元の定数関手の右随伴（補題 3.2）。
方針：局所化した前合成随伴を導来定数随伴に合成し、指定定数同型を使う。
規約：余終性を別の公理として要求しない。使われ方：実際のホモトピー極限の添字変更。 -/
def restrictedHomotopyAdjunction {a : K ⥤ L} {b : L ⥤ K} (adj : a ⊣ b)
    (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _) :
    HomotopyLimit.localizedConstant L Λ QL ⊣
      localized QK QL a ⋙ (homotopyData K I J Λ QK).rightFunctor :=
  ((homotopyAdjunction K I J Λ QK hcof).comp (adjunction QK QL adj)).ofNatIsoLeft
    (constantIso QL QK Λ b)

/-- 概要：左随伴な添字変更は実際のホモトピー極限を自然同定（補題 3.2）。
方針：相関した二つの導来計算、右随伴の一意性、指定局所化比較を合成する。
規約：局所化後の自然同型であり、指定増強との可換式は別に検査する。
使われ方：分裂降下の添字変更とその増強の計算。 -/
def homotopyLimitIso {a : K ⥤ L} {b : L ⥤ K} (adj : a ⊣ b)
    (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _) :
    HomotopyCones.functor L I J ⋙ Λ ≅ precomp a ⋙ HomotopyCones.functor K I J ⋙ Λ :=
  homotopyComputationIso L I J Λ QL ≪≫
    Functor.isoWhiskerLeft QL
      ((homotopyAdjunction L I J Λ QL hcof).rightAdjointUniq
        (restrictedHomotopyAdjunction K I J Λ QK L QL adj hcof)) ≪≫
    Functor.isoWhiskerRight (comparison QK QL a).symm
      (homotopyData K I J Λ QK).rightFunctor ≪≫
    Functor.isoWhiskerLeft (precomp a) (homotopyComputationIso K I J Λ QK).symm

/-- 概要：図式の局所化を内部構成した実際のホモトピー極限の添字変更（補題 3.2）。
方針：点ごとの弱同値の Mathlib の実際の局所化を比較定理へ渡す。
規約：局所化した図式圏の追加入力は不要。使われ方：分裂余単体対象への適用。 -/
def homotopyLimitCanonicalIso {a : K ⥤ L} {b : L ⥤ K} (adj : a ⊣ b)
    (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _) :
    HomotopyCones.functor L I J ⋙ Λ ≅ precomp a ⋙ HomotopyCones.functor K I J ⋙ Λ :=
  homotopyLimitIso K I J Λ (Projective.objectwise K (weakEquivalences SSet.{u})).Q
    L (Projective.objectwise L (weakEquivalences SSet.{u})).Q adj hcof

end SerrePositivity.KST.Descent.CechReindex
