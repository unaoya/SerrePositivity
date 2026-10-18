module
public import SerrePositivity.InfinityCategories.Stable.CofiberTriangle

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
namespace SerrePositivity.InfinityCategories

/-- 概要：接続射と可換な二つの成分は cofiber 三角形の第三射とも可換。
方針：接続射の式を一回シフトとの比較の自然性で輸送する。
規約：三角形の最初の二射の可換性は不要。使われ方：最後の第三射の合成式。 -/
lemma cofiberTriangle_mor₃_naturality {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t d : ZeroTriangle X) (ht : IsCofiberSequence t) (hd : IsCofiberSequence d)
    (a : t.hoShortComplex.X₁ ⟶ d.hoShortComplex.X₁)
    (c : t.hoShortComplex.X₃ ⟶ d.hoShortComplex.X₃)
    (h : c ≫ cofiberConnecting d hd = cofiberConnecting t ht ≫ (suspensionFunctor X).map a) :
    c ≫ (cofiberTriangle d hd).mor₃ =
      (cofiberTriangle t ht).mor₃ ≫ (shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map a := by
  change c ≫ (cofiberConnecting d hd ≫ _) = (cofiberConnecting t ht ≫ _) ≫ _
  rw [← Category.assoc, h, Category.assoc, (shiftOneSuspensionIso X).inv.naturality,
    ← Category.assoc]

end SerrePositivity.InfinityCategories
