module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CountableSimplexStages
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertexNaturality
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
概要：最小所属段階のコンマ圏を有限段階の反対単体圏と比較する。
方針：上界への射を所属証明として読み、包含と所属証明の付け直しを逆関手にする。
規約：単体作用素と次数は変更せず、元の有限段階の包含と可換にする。
使われ方：可算列に沿う局所左 Kan の形状を有限形状の単体圏へ置き換える。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：段階のコンマ圏から有限段階の反対単体圏への関手。
方針：上界への射から単体の所属証明を回収する。
規約：元の単体作用素を保持する。使われ方：局所左 Kan 図式の制限。 -/
def countableStageCommaToSimplex (X : SSet.{u}) [Countable X.S] (n : ℕ) :
    CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor X) (ULift.up n) ⥤
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage X n).toSSet)ᵒᵖ where
  obj a := Opposite.op (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex
    ⟨a.left.unop.objDown.val,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor_le_iff X a.left n).1 (leOfHom a.hom)⟩)
  map f := Quiver.Hom.op ⟨{
    hom := f.left.unop.down.hom
    map_val := Subtype.ext f.left.unop.down.map_val }⟩
  map_id _ := by rfl
  map_comp _ _ := by rfl

/-- 概要：有限段階の単体を段階関手のコンマ圏へ含める。
方針：元の包含で単体を写し、その所属証明から上界への射を付ける。
規約：上界への射は順序圏の一意な射。使われ方：コンマ圏との逆比較。 -/
def countableStageSimplexToComma (X : SSet.{u}) [Countable X.S] (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage X n).toSSet)ᵒᵖ ⥤
      CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor X) (ULift.up n) where
  obj s := CostructuredArrow.mk (homOfLE
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor_le_iff X
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage X n).ι).op.obj s) n).2
        s.unop.objDown.val.property))
  map f := CostructuredArrow.homMk
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage X n).ι).op.map f)
    (Subsingleton.elim _ _)
  map_id _ := by apply CostructuredArrow.ext; rfl
  map_comp _ _ := by apply CostructuredArrow.ext; rfl

/-- 概要：段階のコンマ圏は有限段階の反対単体圏と同値。
方針：所属証明を忘れる操作と付ける操作が互いに逆であることを使う。
規約：単体と単体作用素の実際の値は保存する。
使われ方：有限段階の局所化をコンマ圏へ移す。 -/
def countableStageCommaEquivalence (X : SSet.{u}) [Countable X.S] (n : ℕ) :
    CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor X) (ULift.up n) ≌
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage X n).toSSet)ᵒᵖ where
  functor := countableStageCommaToSimplex X n
  inverse := countableStageSimplexToComma X n
  unitIso := NatIso.ofComponents (fun a ↦ CostructuredArrow.isoMk (Iso.refl _))
    (by intro a b f; apply CostructuredArrow.ext; rfl)
  counitIso := NatIso.ofComponents (fun s ↦ Iso.refl _) (by intro a b f; rfl)
  functor_unitIso_comp _ := by rfl

/-- 概要：逆比較とコンマ圏の射影の合成は元の有限段階の包含。
方針：所属証明を忘れた後の対象と射を展開する。
規約：同型を介さない関手の等式。使われ方：制限図式そのものの同定。 -/
lemma countableStageSimplexToComma_proj (X : SSet.{u}) [Countable X.S] (n : ℕ) :
    countableStageSimplexToComma X n ⋙
      CostructuredArrow.proj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStageFunctor X) (ULift.up n) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage X n).ι).op := rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
