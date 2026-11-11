module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.LeftFibrationTerminalFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEndpointFibration

/-!
概要：基底の辺を固定した coslice の fiber の射影。
方針：相対 coslice の left fibration の充填を固定した基底の辺へ制限する。
規約：点は任意の Δ[0] からの射で指定する。
使われ方：Kerodon §5.1.1（Tag 01T4）・§7.1.5（Tag 02WE） の固定した基底の辺の上の射の空間。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：基底の辺を固定した coslice の fiber から終点の fiber への射影。
方針：coslice の終点射影を fiber の普遍性で制限する。
規約：ファイブレーション性は定義には不要。
使われ方：Kerodon §5.1.1（Tag 01T4） の固定した基底の辺の上の射。 -/
def cosliceFiberProjection {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ p)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p) s ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p) s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) (by
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a ≫ p =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p) := rfl
    rw [Category.assoc, h, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp])

/-- 概要：coslice の fiber の射影を元へ含めると元の終点射影。
方針：fiber への持ち上げの定義を計算する。
規約：全次数で厳密な等式。
使われ方：Kerodon §5.1.1（Tag 01T4） の相対充填の比較。 -/
lemma cosliceFiberProjection_ι {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ p)) _⦋0⦌) :
    cosliceFiberProjection a p s ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p) s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a := rfl

/-- 概要：inner fibration の基底の辺を固定した coslice の射影は left fibration。
方針：相対 coslice の射の持ち上げに定値の基底の辺を指定し、fiber に戻す。
規約：元・標的の quasicategory 性は不要。
使われ方：Kerodon §5.1.1（Tag 01T4） の輸送による射の空間の比較。 -/
instance cosliceFiberProjection_leftFibration {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [InnerFibration p]
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ p)) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (cosliceFiberProjection a p s) where
  mem := by
    intro A D i hi
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap a p) i hi
    constructor
    intro f b sq
    let y := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s
    let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p
    have hbase : (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p y) ≫ p =
        (SSet.const s : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ p)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p) := by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp, SSet.comp_const]
    let T := pullback.lift (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p y) (SSet.const s) hbase
    have hw : (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q s) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap a p = i ≫ T := by
      apply pullback.hom_ext
      · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap_fst, T, pullback.lift_fst]
        have hh := congrArg (fun t ↦ t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p y) sq.w
        rw [Category.assoc, cosliceFiberProjection_ι, ← Category.assoc] at hh
        exact hh
      · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap_snd, T, pullback.lift_snd]
        change f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q s ≫ q = i ≫ SSet.const s
        simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
    let hs : CommSq (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q s) i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap a p) T := ⟨hw⟩
    have hfix : hs.lift ≫ q = SSet.const s := by
      have hh := congrArg (fun t ↦ t ≫ pullback.snd p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p))) hs.fac_right
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap_snd, T, pullback.lift_snd] at hh
      exact hh
    refine CommSq.HasLift.mk' {
      l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q s hs.lift hfix
      fac_left := ?_
      fac_right := ?_ }
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q s
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
      exact hs.fac_left
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p y
      rw [Category.assoc, cosliceFiberProjection_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
      have hh := congrArg (fun t ↦ t ≫ pullback.fst p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p))) hs.fac_right
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap_fst, T, pullback.lift_fst] at hh
      exact hh

/-- 概要：cocartesian な辺の始点から fiber の終対象へ向かう固定基底上の射の空間は可縮。
方針：cocartesian な持ち上げが与える始対象と left fibration の終対象上の fiber の充填を使う。
規約：元・標的の quasicategory 性は不要。
使われ方：Kerodon §7.1.5（Tag 02WE） の fiber の終対象から相対終対象への接続。 -/
lemma cosliceFiberProjection_terminalFiber_isContractibleKan {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p]
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ p)) _⦋0⦌)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s)) _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (cosliceFiberProjection a p s) x) := by
  obtain ⟨t, ht, hp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_cocartesianCosliceVertex_lift a p s
  let t' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p) s) _⦋0⦌ := ⟨t, by
    have h0 : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := Subsingleton.elim _ _
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant, h0, op_id,
      CategoryTheory.Functor.map_id_apply] using hp⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.leftFibration_terminalFiber_isContractibleKan (cosliceFiberProjection a p s)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInitialVertex_cocartesianCosliceFiber a p s t' ht) hx

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
