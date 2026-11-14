module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberTriangle

/-! # 接続射の可換式を三角形の第三射へ移す

概要：懸垂に値を取る接続射の可換式は一回シフトに値を取る第三射の可換式となる。
方針：一回シフトと懸垂の自然同型の自然性を適用する。
規約：射の表現や図式のホモトピーを追加仮定しない。使われ方：八面体の第三射の合成表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：接続射と可換な二つの成分は cofiber 三角形の第三射とも可換。
方針：接続射の式を一回シフトとの比較の自然性で輸送する。
規約：三角形の最初の二射の可換性は不要。使われ方：最後の第三射の合成式。 -/
lemma cofiberTriangle_mor₃_naturality {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t) (hd : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence d)
    (a : t.hoShortComplex.X₁ ⟶ d.hoShortComplex.X₁)
    (c : t.hoShortComplex.X₃ ⟶ d.hoShortComplex.X₃)
    (h : c ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting d hd = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map a) :
    c ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle d hd).mor₃ =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht).mor₃ ≫ (shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map a := by
  change c ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting d hd ≫ _) = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ _) ≫ _
  rw [← Category.assoc, h, Category.assoc, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.naturality,
    ← Category.assoc]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
