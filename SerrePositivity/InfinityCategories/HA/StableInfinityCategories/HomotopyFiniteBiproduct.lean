module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyPreadditive
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # 安定ホモトピー圏の有限双積

概要：h C は空族も含めた全ての有限双積を持つ。
方針：二項積と零対象から有限積を作り、前加法性で有限双積にする。
規約：∞ 圏自体の全有限極限の存在とは別の主張。使われ方：h C の加法圏構造。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：安定ホモトピー圏は有限積を持つ。
方針：二項積と零対象の終対象性から有限積を作る。
規約：h C での有限積。使われ方：有限双積の構成。 -/
instance hasFiniteProducts_ho {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    HasFiniteProducts (hoFunctor.obj X) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- 概要：安定ホモトピー圏は全ての有限双積を持つ。
方針：前加法圏における有限積から有限双積を得る。
規約：空族の双積は既存の零対象。使われ方：加法圏としての三角構造。 -/
instance hasFiniteBiproducts_ho {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    HasFiniteBiproducts (hoFunctor.obj X) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
