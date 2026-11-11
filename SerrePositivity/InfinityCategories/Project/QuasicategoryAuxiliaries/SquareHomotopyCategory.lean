module
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroHomotopy

/-! # 四角形と零角の列のホモトピー圏での像

概要：単体的な四角形は h C の可換四角形を与え、零角を持てば二辺の合成が零になる。
方針：区間の辺と恒等辺の積で四辺を作り、二つの合成三角形を共通の対角で比較する。
規約：下辺の後に右辺を合成する。加法構造や安定性は仮定しない。
使われ方：S4 の cofiber 三角形の最初の二射と S5 の完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：零頂点を持つ quasicategory の h C に零射を入れる。
方針：構成済みの零対象を通る一意の射を使う。
規約：Mathlib の零対象からの標準構成。使われ方：短複体と加法構造の零射。 -/
instance hasZeroMorphisms_ho {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] :
    HasZeroMorphisms (hoFunctor.obj X) :=
  HasZeroObject.zeroMorphismsOfZeroObject (C := hoFunctor.obj X)

/-- 概要：四角形の下辺を、端点を固定した実際の辺として取り出す。
方針：横方向の区間と縦方向の始点の恒等辺を写す。
規約：(0,0) から (1,0)。使われ方：cofiber 列の第一射。 -/
def squareBottomArrow {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    SSet.Truncated.Edge (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
    (X := (truncation 2).obj (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 0))).map
      ((truncation 2).map F)

/-- 概要：四角形の右辺を端点つきの辺として取り出す。
方針：横方向の終点の恒等辺と縦方向の区間を写す。
規約：(1,0) から (1,1)。使われ方：cofiber 列の第二射。 -/
def squareRightArrow {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    SSet.Truncated.Edge (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 1) :=
  ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
    (stdSimplex.obj₀Equiv.symm 1)).tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map F)

/-- 概要：四角形の左辺を端点つきの辺として取り出す。
方針：横方向の始点の恒等辺と縦方向の区間を写す。
規約：(0,0) から (0,1)。使われ方：零対象を通る合成。 -/
def squareLeftArrow {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    SSet.Truncated.Edge (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 1) :=
  ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
    (stdSimplex.obj₀Equiv.symm 0)).tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map F)

/-- 概要：四角形の上辺を端点つきの辺として取り出す。
方針：横方向の区間と縦方向の終点の恒等辺を写す。
規約：(0,1) から (1,1)。使われ方：零対象を通る合成。 -/
def squareTopArrow {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    SSet.Truncated.Edge (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 1) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 1) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
    (X := (truncation 2).obj (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 1))).map
      ((truncation 2).map F)

/-- 概要：単体的四角形の四辺の類は h C の可換四角形をなす。
方針：二つの合成二単体を同じ対角辺の類と比較する。
規約：quasicategory 性は不要。使われ方：三角形の合成零の証明。 -/
lemma square_homMk_comm {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    SSet.Truncated.HomotopyCategory.homMk (squareBottomArrow F) ≫
      SSet.Truncated.HomotopyCategory.homMk (squareRightArrow F) =
    SSet.Truncated.HomotopyCategory.homMk (squareLeftArrow F) ≫
      SSet.Truncated.HomotopyCategory.homMk (squareTopArrow F) := by
  let t₀ := ((SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
    (SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).map ((truncation 2).map F)
  let t₁ := ((SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
    (SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).map ((truncation 2).map F)
  exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk t₀).trans
    (SSet.Truncated.HomotopyCategory.homMk_comp_homMk t₁).symm

/-- 概要：四角形の角のホモトピー圏の対象。
方針：頂点を h C に写す。規約：束ねた hoFunctor の値域を明示する。
使われ方：零射構造と四辺の類の型を揃える。 -/
def squareHoVertex {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (i j : Fin 2) : hoFunctor.obj X := SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F i j)

/-- 概要：四角形の辺のホモトピー類。
方針：端点つきの辺を商に写す。規約：h C の射。
使われ方：四角形の可換性と零角の短複体。 -/
def squareHoBottom {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    @Quiver.Hom (hoFunctor.obj X) _ (squareHoVertex F 0 0) (squareHoVertex F 1 0) :=
  SSet.Truncated.HomotopyCategory.homMk (squareBottomArrow F)

/-- 概要：四角形の辺のホモトピー類。
方針：端点つきの辺を商に写す。規約：h C の射。
使われ方：四角形の可換性と零角の短複体。 -/
def squareHoRight {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    @Quiver.Hom (hoFunctor.obj X) _ (squareHoVertex F 1 0) (squareHoVertex F 1 1) :=
  SSet.Truncated.HomotopyCategory.homMk (squareRightArrow F)

/-- 概要：四角形の辺のホモトピー類。
方針：端点つきの辺を商に写す。規約：h C の射。
使われ方：四角形の可換性と零角の短複体。 -/
def squareHoLeft {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    @Quiver.Hom (hoFunctor.obj X) _ (squareHoVertex F 0 0) (squareHoVertex F 0 1) :=
  SSet.Truncated.HomotopyCategory.homMk (squareLeftArrow F)

/-- 概要：四角形の辺のホモトピー類。
方針：端点つきの辺を商に写す。規約：h C の射。
使われ方：四角形の可換性と零角の短複体。 -/
def squareHoTop {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    @Quiver.Hom (hoFunctor.obj X) _ (squareHoVertex F 0 1) (squareHoVertex F 1 1) :=
  SSet.Truncated.HomotopyCategory.homMk (squareTopArrow F)

/-- 概要：零角の四角形の下辺と右辺の合成は h C で零となる。
方針：可換性で左上の零対象を通る合成へ移す。
規約：任意の零射構造を使え、安定性や普遍性は不要。
使われ方：cofiber 列を三角形にする最初の二射。 -/
lemma ZeroTriangle.homMk_comp_eq_zero {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) :
    squareHoBottom t.square ≫ squareHoRight t.square = 0 := by
  have h : squareHoBottom t.square ≫ squareHoRight t.square =
      squareHoLeft t.square ≫ squareHoTop t.square := square_homMk_comm t.square
  rw [h, t.zero_corner.isZeroHo.eq_zero_of_src (C := hoFunctor.obj X)
    (squareHoTop t.square), comp_zero (C := hoFunctor.obj X)]

/-- 概要：零角の四角形は h C の短複体を与える。
方針：左下、右下、右上を対象とし、二辺の類と合成零の証明を組にする。
規約：cofiber/fiber の普遍性はこの定義には不要。
使われ方：S4 の三角形の基礎と S5 の Hom 完全性。 -/
def ZeroTriangle.hoShortComplex {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) : ShortComplex (hoFunctor.obj X) where
  X₁ := squareHoVertex t.square 0 0
  X₂ := squareHoVertex t.square 1 0
  X₃ := squareHoVertex t.square 1 1
  f := squareHoBottom t.square
  g := squareHoRight t.square
  zero := t.homMk_comp_eq_zero

/-- 概要：端点つき下辺の一次単体は下辺の制限の Yoneda 表示に一致する。
方針：区間の恒等単体と定値単体を比較する。
規約：端点の命題的等号の輸送を含まない。使われ方：指定射との比較。 -/
lemma squareBottomArrow_edge {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (squareBottomArrow F).edge = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F) := by
  change F.app _ (_, _) = F.app _ (_, _)
  congr 1
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 概要：端点つき右辺の一次単体は右辺の制限の Yoneda 表示に一致する。
方針：定値単体と区間の恒等単体を比較する。
規約：端点の輸送を含まない。使われ方：指定射との比較。 -/
lemma squareRightArrow_edge {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (squareRightArrow F).edge = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F) := by
  change F.app _ (_, _) = F.app _ (_, _)
  congr 1
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 概要：指定射の cofiber 四角形から得た短複体の第一射はその射の類。
方針：下辺の固定条件と辺の類の Arrow 表示の等式を用いる。
規約：端点の等式による輸送を Arrow の等号に含める。
使われ方：S4 の任意の射を含む cofiber 三角形。 -/
lemma CofiberSquare.hoShortComplex_f_arrow {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] {x y : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y} (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) :
    Arrow.mk s.toZeroTriangle.hoShortComplex.f =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk f) := by
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [squareBottomArrow_edge, s.bottom_edge]
  exact SSet.yonedaEquiv.apply_symm_apply f.edge

/-- 概要：指定射の fiber 四角形から得た短複体の第二射はその射の類。
方針：右辺の固定条件と辺の類の Arrow 表示を比較する。
規約：端点の等号による輸送を含む。使われ方：fiber 列の第二射の照合。 -/
lemma FiberSquare.hoShortComplex_g_arrow {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] {x y : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y} (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f) :
    Arrow.mk s.toZeroTriangle.hoShortComplex.g =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk f) := by
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [squareRightArrow_edge, s.right_edge]
  exact SSet.yonedaEquiv.apply_symm_apply f.edge

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
