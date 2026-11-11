module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Suspension
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Loop

/-! # Suspension と loop の逆性

概要：安定 ∞ 圏のホモトピー圏で Σ と Ω は互いに逆な圏同値をなす。
方針：始点評価と終点評価の同値の間に、安定性による普遍四角形の族の同型を挟む。
規約：順方向と逆方向を、既に構成した suspensionFunctor と loopFunctor に厳密に合わせる。
使われ方：S3 の自己同値と S4 のシフト。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：安定性による普遍四角形の族の同型は quasicategory の同値。
方針：単体集合の同型の両逆性を可逆二胞体へ移す。
規約：実際の四角形は変えない。
使われ方：Σ と Ω の評価の同値を結ぶ。 -/
def suspensionLoopDiagramEquivalence (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) where
  hom := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopDiagramsIso X).hom
  inv := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopDiagramsIso X).inv
  homInvIso := eqToIso (congrArg (fun f ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopDiagramsIso X).hom_inv_id)
  invHomIso := eqToIso (congrArg (fun f ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopDiagramsIso X).inv_hom_id)

/-- 概要：始点と終点の評価の間を普遍四角形の族で結んだ C の自己同値。
方針：suspension の始点評価の逆、図式の同型、loop の終点評価を合成する。
規約：この段階では単体的な同値を構成する。
使われ方：ホモトピー圏の ΣΩ の単位・余単位。 -/
def suspensionQCatEquivalence (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X X :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence X).symm.trans
    ((suspensionLoopDiagramEquivalence X).trans (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramTargetEquivalence X))

/-- 概要：自己同値の順方向は suspension 図式の選択と右上評価の合成。
方針：図式の族の同型と評価の可換性を使う。
規約：単体集合の射の等式。
使われ方：既存の suspensionFunctor との照合。 -/
lemma suspensionQCatEquivalence_hom (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    (suspensionQCatEquivalence X).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence X).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1 := by
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence X).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopDiagramsIso X).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopDiagramsIso_evaluation]

/-- 概要：自己同値の逆方向は loop 図式の選択と左下評価の合成。
方針：図式の逆同型も四角形の各角を保つことを使う。
規約：単体集合の射の等式。
使われ方：既存の loopFunctor との照合。 -/
lemma suspensionQCatEquivalence_inv (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    (suspensionQCatEquivalence X).inv =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramTargetEquivalence X).inv ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0 := by
  change ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramTargetEquivalence X).inv ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopDiagramsIso X).inv) ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0 = _
  rw [Category.assoc]
  rfl

/-- 概要：単体的自己同値のホモトピー関手は構成済みの Σ 関手。
方針：順方向の射の式と h の合成則を使う。
規約：関手の等式。
使われ方：圏同値の順方向を指定した定義に合わせる。 -/
lemma suspensionQCatEquivalence_ho_functor (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    (suspensionQCatEquivalence X).toHoEquivalence.functor = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.toHoEquivalence_functor, suspensionQCatEquivalence_hom,
    CategoryTheory.Functor.map_comp, Cat.Hom.comp_toFunctor]
  rfl

/-- 概要：単体的自己同値の逆のホモトピー関手は構成済みの Ω 関手。
方針：逆方向の射の式と h の合成則を使う。
規約：関手の等式。
使われ方：圏同値の逆方向を指定した定義に合わせる。 -/
lemma suspensionQCatEquivalence_ho_inverse (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    (suspensionQCatEquivalence X).toHoEquivalence.inverse = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopFunctor X := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.toHoEquivalence_inverse, suspensionQCatEquivalence_inv,
    CategoryTheory.Functor.map_comp, Cat.Hom.comp_toFunctor]
  rfl

/-- 概要：安定 ∞ 圏のホモトピー圏で Σ は Ω を逆関手に持つ自己同値。
方針：普遍四角形の族を介した単体的自己同値の単位と余単位を、構成済みの二関手に移す。
規約：順方向は suspensionFunctor、逆方向は loopFunctor。
使われ方：S3 の主定理と S4 の整数シフトの構成。 -/
def suspensionEquivalence (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    hoFunctor.obj X ≌ hoFunctor.obj X :=
  CategoryTheory.Equivalence.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopFunctor X)
    (by simpa only [suspensionQCatEquivalence_ho_functor,
      suspensionQCatEquivalence_ho_inverse] using
      (suspensionQCatEquivalence X).toHoEquivalence.unitIso)
    (by simpa only [suspensionQCatEquivalence_ho_functor,
      suspensionQCatEquivalence_ho_inverse] using
      (suspensionQCatEquivalence X).toHoEquivalence.counitIso)

/-- 概要：自己同値の順方向は Σ 関手そのもの。
方針：構成の定義を計算する。
規約：関手の等式。使われ方：シフトとの照合。 -/
lemma suspensionEquivalence_functor (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    (suspensionEquivalence X).functor = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X := rfl

/-- 概要：自己同値の逆方向は Ω 関手そのもの。
方針：構成の定義を計算する。
規約：関手の等式。使われ方：逆シフトとの照合。 -/
lemma suspensionEquivalence_inverse (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    (suspensionEquivalence X).inverse = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopFunctor X := rfl

/-- 概要：恒等関手から Σ の後に Ω を施す関手への自然同型。
方針：構成した自己同値の単位を取る。
規約：関手の合成は左から右。
使われ方：S3 の ΣΩ の逆性と整数シフトの単位。 -/
def suspensionLoopUnitIso (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    𝟭 (hoFunctor.obj X) ≅ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X ⋙ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopFunctor X :=
  (suspensionEquivalence X).unitIso

/-- 概要：Ω の後に Σ を施す関手から恒等関手への自然同型。
方針：構成した自己同値の余単位を取る。
規約：関手の合成は左から右。
使われ方：S3 の ΣΩ の逆性と整数シフトの余単位。 -/
def loopSuspensionCounitIso (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopFunctor X ⋙ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X ≅ 𝟭 (hoFunctor.obj X) :=
  (suspensionEquivalence X).counitIso

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
