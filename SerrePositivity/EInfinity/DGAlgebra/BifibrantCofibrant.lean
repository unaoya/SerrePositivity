module

public import SerrePositivity.EInfinity.DGAlgebra.ModelCategory
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ModelBifibrantRelative

/-!
概要：実 dg 代数では cofibrant 全部分圏と bifibrant 全部分圏が同じ底を持つ。
方針：証明済みの allFibrant を各対象に使い、元の射をそのまま持ち上げる。
規約：fibrant 置換を選ばず、大域 instance を追加しない。
使われ方：Sp への bifibrant 中継の実 dg モデルへの代入。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.DGAlgebra
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R]
attribute [local instance] hasFiniteLimits hasTerminal

/-- 概要：実 cofibrant dg 代数を同じ底の bifibrant 対象へ持ち上げる。
方針：同じモデルの allFibrant を代入する。
規約：対象と射を置換しない。使われ方：実 bifibrant frame の比較。 -/
def cofibrantToBifibrant :
    let := modelCategory R
    CofibrantObject (Mon (Complex R)) ⥤ BifibrantObject (Mon (Complex R)) := by
  let := modelCategory R
  exact (bifibrantObjects (Mon (Complex R))).lift CofibrantObject.ι
    (fun X => ⟨X.property, allFibrant R X.obj⟩)

/-- 概要：実 dg モデルの cofibrant・bifibrant 全部分圏は同じ射による圏同値。
方針：元の包含を逆にし、両合成の定義上の恒等を使う。
規約：fibrant 置換なし。使われ方：全 dg 代数の供給での余分な置換の除去。 -/
def cofibrantBifibrantEquivalence :
    let := modelCategory R
    CofibrantObject (Mon (Complex R)) ≌ BifibrantObject (Mon (Complex R)) := by
  let := modelCategory R
  exact CategoryTheory.Equivalence.mk (cofibrantToBifibrant R) BifibrantObject.ιCofibrantObject
    (eqToIso rfl) (eqToIso rfl)

/-- 概要：同じ bifibrant 化の底の対象・全射は元の包含そのもの。
方針：持ち上げの定義を読む。
規約：全関手の定義上の等式。使われ方：実 dg 代数の元の frame の回収。 -/
lemma cofibrantToBifibrant_inclusion :
    let := modelCategory R
    cofibrantToBifibrant R ⋙ BifibrantObject.ι = CofibrantObject.ι := rfl

end SerrePositivity.EInfinity.DGAlgebra
