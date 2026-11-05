module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.FundamentalNerveTranspose
public import SerrePositivity.InfinityCategories.Core.HomotopyNatTrans
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-! # nerve 値ホモトピーから転置した関手の自然同型
概要：亜群の nerve を標的とする実際のホモトピーを、戻した関手の自然同型へ移す。
方針：ホモトピー圏の自然変換を nerve 随伴の余単位で後合成する。
規約：元の単体的ホモトピーを使う。使われ方：基本亜群と Kan 置換の比較の逆律。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- nerve 値写像を戻す操作はホモトピー圏の射と余単位の合成そのもの。 -/
lemma fundamentalNerveUntranspose_eq {A : SSet.{u}} {C : Type u} [Category.{u} C]
    (f : A ⟶ nerve C) :
    fundamentalNerveUntranspose f =
      (hoFunctor.map f).toFunctor ⋙ (nerveAdjunction.counit.app (Cat.of C)).toFunctor := rfl

/-- 亜群 nerve 値ホモトピーは転置した通常の関手の自然同型を与える。 -/
def fundamentalNerveUntransposeHomotopy {A : SSet.{u}} {C : Type u}
    [Category.{u} C] [IsGroupoid C] {f g : A ⟶ nerve C} (H : SSet.Homotopy f g) :
    fundamentalNerveUntranspose f ≅ fundamentalNerveUntranspose g := by
  let α := homotopyNatTransOfEndpoints H.h H.h₀ H.h₁
  have : IsIso α := (NatTrans.isIso_iff_isIso_app α).mpr (fun _ => inferInstance)
  exact Functor.isoWhiskerRight (asIso α) (nerveAdjunction.counit.app (Cat.of C)).toFunctor

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.fundamentalNerveUntransposeHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalNerveUntransposeHomotopy := _root_.SerrePositivity.InfinityCategories.Kan.fundamentalNerveUntransposeHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalNerveUntranspose_eq := _root_.SerrePositivity.InfinityCategories.Kan.fundamentalNerveUntranspose_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalNerveUntransposeHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.fundamentalNerveUntransposeHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalNerveUntransposeHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.fundamentalNerveUntransposeHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.fundamentalNerveUntransposeHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.fundamentalNerveUntransposeHomotopy._proof_3
