module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSuspensionComparison

/-! # Cofiber 列の接続射

概要：cofiber 列 X → Y → Z から h C の接続射 Z → ΣX を構成する。
方針：始点固定の suspension への比較を短複体の射に移し、第三成分を取る。
規約：比較ホモトピーは古典的に選択する。選択からの独立性は別途証明する。
使われ方：S4 の cofiber 三角形の第三射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：指定した suspension 四角形への始点固定の比較を一つ選ぶ。
方針：存在定理から古典的に選択する。
規約：元の四角形は押し出し。使われ方：接続射の具体的な定義。 -/
def chosenCofiberSuspensionComparison {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0)) : SSet.Homotopy F s.square :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_cofiberSuspensionComparison F hF s)

/-- 概要：選んだ比較ホモトピーは元の始点を全パラメーターで固定する。
方針：選択の付随条件を読む。
規約：始点の射は厳密に定値。使われ方：接続射の選択の比較と自然性。 -/
lemma chosenCofiberSuspensionComparison_source {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0)) :
    ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (chosenCofiberSuspensionComparison F hF s).h =
        CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0) :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_cofiberSuspensionComparison F hF s)

/-- 概要：cofiber 列から指定した suspension 列への短複体の比較射。
方針：選んだ始点固定の比較ホモトピーを h C に移す。
規約：第一成分の始点固定条件も比較ホモトピーとして保持する。
使われ方：第三成分で接続射を得る。 -/
def cofiberSuspensionShortComplexMap {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    t.hoShortComplex ⟶ s.toZeroTriangle.hoShortComplex :=
  let Q := chosenCofiberSuspensionComparison t.square ht s
  t.hoShortComplexMapOfHomotopy s.toZeroTriangle Q.h Q.h₀ Q.h₁

/-- 概要：cofiber 対象から指定した suspension 四角形の頂点への接続射。
方針：短複体の比較射の第三成分を取る。
規約：Σ の関手の対象との比較は次の定義で行う。使われ方：接続射の零合成。 -/
def cofiberConnectingToSuspension {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    t.hoShortComplex.X₃ ⟶ SSet.HomotopyCategory.mk s.vertex :=
  (cofiberSuspensionShortComplexMap t ht s).τ₃

/-- 概要：cofiber 列の第二射と suspension 頂点への接続射の合成は零。
方針：短複体の比較射の可換性を使い、suspension の右下の零対象を通る合成へ移す。
規約：任意の指定した suspension 四角形。使われ方：三角形の隣り合う射の零合成。 -/
lemma cofiberConnectingToSuspension_comp_eq_zero {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    t.hoShortComplex.g ≫ cofiberConnectingToSuspension t ht s = 0 := by
  let m := cofiberSuspensionShortComplexMap t ht s
  change t.hoShortComplex.g ≫ m.τ₃ = 0
  rw [← m.comm₂₃, s.other_zero.isZeroHo.eq_zero_of_tgt (C := hoFunctor.obj X) m.τ₂,
    zero_comp (C := hoFunctor.obj X)]

/-- 概要：安定 ∞ 圏の cofiber 列は Z → ΣX の接続射を持つ。
方針：suspension 四角形を選び、その頂点を構成済みの suspensionFunctor の値と同定する。
規約：接続射の選択独立性と三角圏の公理はまだ主張しない。
使われ方：S4 の distinguished triangle の第三射。 -/
def cofiberConnecting {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    t.hoShortComplex.X₃ ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).obj t.hoShortComplex.X₁ :=
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)
  cofiberConnectingToSuspension t ht s ≫ s.suspensionFunctorObjIso.inv

/-- 概要：cofiber 列の第二射の後に接続射を合成すると零。
方針：指定 suspension への零合成を対象の比較同型で移す。
規約：安定 ∞ 圏。使われ方：cofiber 三角形の零合成。 -/
lemma cofiberConnecting_comp_eq_zero {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    t.hoShortComplex.g ≫ cofiberConnecting t ht = 0 := by
  change t.hoShortComplex.g ≫ (cofiberConnectingToSuspension t ht _ ≫ _) = 0
  rw [← Category.assoc, cofiberConnectingToSuspension_comp_eq_zero,
    zero_comp (C := hoFunctor.obj X)]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
