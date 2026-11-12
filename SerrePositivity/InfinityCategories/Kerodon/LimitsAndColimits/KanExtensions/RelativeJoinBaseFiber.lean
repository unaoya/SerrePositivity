module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseHomFiberNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPullbackIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteTotalFibers

/-!
概要：相対 join の底の頂点上の fiber を、元の fiber の通常の余錐と同定する。
方針：底変換との交換、一点上の relative join の計算、頂点 fiber の pullback 表示を合成する。
規約：充填性を仮定しない strict な同型。
使われ方：fiber ごとの普遍余錐性を関手の族の制限の fiber で読み取る。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：相対 join の左包含は係数の底への射影を保つ。
方針：引き戻しの第二射影と prism の係数を計算する。
規約：両方の構造射は任意。
使われ方：左包含が各底の頂点の fiber に誘導する射。 -/
lemma kanRelativeJoinInl_baseProjection {K L C : SSet.{u}} (p : K ⟶ C) (q : L ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p q = p := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl, pullback.lift_snd,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_snd, Category.comp_id]

/-- 概要：相対 join の底変換は左因子の包含と可換。
方針：二つの pullback 射影で join の左包含と prism の自然性を使う。
規約：底変換の射は任意。
使われ方：底の fiber の同型で左端を厳密に追跡する。 -/
lemma kanRelativeJoinInl_pullbackMap {K C T : SSet.{u}} (p : K ⟶ C) (a : T ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (pullback.snd p a) (𝟙 T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackMap p a =
      pullback.fst p a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C) := by
  apply pullback.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackMap_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_fst]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackMap_snd, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl, pullback.lift_snd]
    rw [Category.assoc (pullback.fst p a) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C)) _,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl, pullback.lift_snd]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, ← Category.assoc]
    exact (congrArg (fun q ↦ q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 C)
      (pullback.condition (f := p) (g := a))).symm.trans (Category.assoc _ _ _)

/-- 概要：底の c 上の相対 join の fiber は K_c⋆Δ⁰ と同型。
方針：底変換後の relative join を一点上の通常の join と同定する。
規約：同型の向きは通常の余錐から相対 join の fiber へ。
使われ方：fiber ごとの普遍余錐の比較。 -/
def kanRelativeJoinBaseFiberIso {K C : SSet.{u}} (p : K ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) (Δ[0] : SSet.{u}) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiber_isPullback p c).isoPullback (Iso.refl (Δ[0] : SSet.{u})) ≪≫
    (asIso (pullback.fst
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (pullback.snd p (SSet.const c : (Δ[0] : SSet.{u}) ⟶ C)) (𝟙 (Δ[0] : SSet.{u})))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal (Δ[0] : SSet.{u})))).symm ≪≫
    asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackLift p (SSet.const c : (Δ[0] : SSet.{u}) ⟶ C)) ≪≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiber_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) c).flip.isoPullback).symm

/-- 概要：fiber 同型を全空間へ含めると、底変換した相対 join の標準射になる。
方針：各同型の射影の計算則。
規約：選択した同型の実際の射を追跡する。
使われ方：余錐の両端の厳密な比較。 -/
lemma kanRelativeJoinBaseFiberIso_hom_ι {K C : SSet.{u}} (p : K ⟶ C) (c : C _⦋0⦌) :
    (kanRelativeJoinBaseFiberIso p c).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiber_isPullback p c).isoPullback.hom (𝟙 (Δ[0] : SSet.{u})) ≫
        inv (pullback.fst
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (pullback.snd p (SSet.const c : (Δ[0] : SSet.{u}) ⟶ C)) (𝟙 (Δ[0] : SSet.{u})))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal (Δ[0] : SSet.{u}))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackMap p (SSet.const c : (Δ[0] : SSet.{u}) ⟶ C) := by
  simp only [kanRelativeJoinBaseFiberIso, Iso.trans_hom, Iso.symm_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso,
    asIso_hom, asIso_inv, Iso.refl_hom, Category.assoc, IsPullback.isoPullback_inv_snd,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackLift_snd]

/-- 概要：fiber の同型の下で左包含は元の fiber の左端包含。
方針：全空間の包含後に比較し、一点上の relative join と底変換の左端を計算する。
規約：厳密な射の等式。
使われ方：fiber の関手空間の制限を coconeRestriction と同定する。 -/
lemma kanRelativeJoinBaseFiberIso_inl {K C : SSet.{u}} (p : K ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) (Δ[0] : SSet.{u}) ≫ (kanRelativeJoinBaseFiberIso p c).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C))
        (kanRelativeJoinInl_baseProjection p (𝟙 C)) c := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) c
  rw [Category.assoc, kanRelativeJoinBaseFiberIso_hom_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc]
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (pullback p (SSet.const c : (Δ[0] : SSet.{u}) ⟶ C)) (Δ[0] : SSet.{u}) ≫
      inv (pullback.fst
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (pullback.snd p (SSet.const c : (Δ[0] : SSet.{u}) ⟶ C)) (𝟙 (Δ[0] : SSet.{u})))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal (Δ[0] : SSet.{u}))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (pullback.snd p (SSet.const c : (Δ[0] : SSet.{u}) ⟶ C))
      (𝟙 (Δ[0] : SSet.{u})) := by
    apply (cancel_mono (pullback.fst _ _)).1
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_fst]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (pullback p (SSet.const c : (Δ[0] : SSet.{u}) ⟶ C)) _) _ _,
    he, kanRelativeJoinInl_pullbackMap, ← Category.assoc,
    IsPullback.isoPullback_hom_fst]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
