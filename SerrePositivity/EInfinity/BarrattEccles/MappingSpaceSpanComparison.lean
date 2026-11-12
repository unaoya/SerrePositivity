module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceSpans
public import SerrePositivity.EInfinity.FrameHom.FrameIndexAugmentation
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FrameIndexComparison

/-!
# 元の E 代数の Map^h への共通比較の反転可能な左射

概要：特殊な三本矢への比較と同じ始域から元の Map^h への射と反転性を構成する。
方針：反対要素圏の終端 augmentation とその宇宙持ち上げを同じ Map^h に適用する。
規約：任意の可換環・任意の元の代数を扱い、単体集合モデルは仮定しない。
使われ方：Dwyer–Kan §7 の E2b の実際の共通比較の左射。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra Opposite
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：同じ共通始域から元の Map^h の持ち上げへの実際の射（Dwyer–Kan §7）。
方針：元の全単体の反対要素圏へ終端 augmentation を適用する。
規約：右射 mappingSpaceSpecialHammockNerveMap と同じ始域。
使われ方：実際の E 代数の高次比較の左射。 -/
def mappingSpaceIndexAugmentation (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      SSet.uliftFunctor.{u + 1, u}.obj (((mappingSpace A).obj (op X)).obj Y) :=
  FrameHom.SimplexTerminalNerve.liftedAugmentation _

/-- 概要：元の Map^h への左射は実際の anodyne 反転後に可逆（Dwyer–Kan §7）。
方針：全単体集合での終端 augmentation の反転性を同じ Hom へ代入する。
規約：元の代数の cofibrancy や単体集合のモデル構造を要求しない。
使われ方：共通比較の左側を反転する。 -/
lemma mappingSpaceIndexAugmentation_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (mappingSpaceIndexAugmentation A X Y)) :=
  FrameHom.SimplexTerminalNerve.liftedAugmentation_localized_isIso _

/-- 概要：左射は元の零単体の同じ持ち上げを回収する（Dwyer–Kan §7）。
方針：終端パラメータの零次の恒等性を同じ Map^h へ適用する。
規約：元の零単体を別の代表に変更しない。
使われ方：元の代数射の類の比較の正規化。 -/
lemma mappingSpaceIndexAugmentation_zero (X Y : (operad A).Algebra)
    (f : (((mappingSpace A).obj (op X)).obj Y) _⦋0⦌) :
    (mappingSpaceIndexAugmentation A X Y).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (show ULiftHom.{u + 1}
          (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ) from
            op ((((mappingSpace A).obj (op X)).obj Y).elementsMk (op ⦋0⦌) f))) =
      ULift.up f :=
  FrameHom.SimplexTerminalNerve.liftedAugmentation_zero _ f

/-- 概要：共通比較の全頂点で両射は元の局所化射を回収する（Dwyer–Kan §7）。
方針：終端パラメータの要素圏射を通す一般の正規化へ元のモデルを局所代入する。
規約：全次数の単体を扱い、元の π₀ 同値を使う。
使われ方：高次比較の両射と元の写像空間の零次の照合。 -/
lemma mappingSpaceSpanComparison_vertex (X Y : (operad A).Algebra)
    (s : ((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ) :
    let := modelCategory A
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.value ((mappingSpaceSpecialHammockFunctor A X Y).obj s) =
      mappingSpacePiZeroEquiv A (weakEquivalences (operad A).Algebra).Q (op X) Y
        (SSet.π₀.mk (((mappingSpaceIndexAugmentation A X Y).app (op ⦋0⦌)
          (ComposableArrows.mk₀ (show ULiftHom.{u + 1}
            (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ) from s))).down)) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.chosenResolutionSpanValue_augmentation (mappingCofibrantFactorization A)
    (mappingFibrantFactorization A) X Y s

end SerrePositivity.EInfinity.BarrattEccles
