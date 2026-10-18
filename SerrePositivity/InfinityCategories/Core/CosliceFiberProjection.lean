module

public import SerrePositivity.InfinityCategories.Core.LeftFibrationTerminalFiber
public import SerrePositivity.InfinityCategories.Core.CosliceEndpointFibration

/-!
概要：基底の辺を固定した coslice の fiber の射影。
方針：相対 coslice の left fibration の充填を固定した基底の辺へ制限する。
規約：点は任意の Δ[0] からの射で指定する。
使われ方：Kerodon §5.1.1・§7.1.5 の固定した基底の辺の上の射の空間。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：基底の辺を固定した coslice の fiber から終点の fiber への射影。
方針：coslice の終点射影を fiber の普遍性で制限する。
規約：ファイブレーション性は定義には不要。
使われ方：Kerodon §5.1.1 の固定した基底の辺の上の射。 -/
def cosliceFiberProjection {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (s : (sliceUnder (a ≫ p)) _⦋0⦌) :
    vertexFiber (sliceUnderPostcomp a p) s ⟶
      vertexFiber p ((sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s) :=
  vertexFiberLift p _ (vertexFiberι (sliceUnderPostcomp a p) s ≫ sliceUnderProjection a) (by
    have h : sliceUnderProjection a ≫ p =
        sliceUnderPostcomp a p ≫ sliceUnderProjection (a ≫ p) := rfl
    rw [Category.assoc, h, ← Category.assoc, vertexFiberι_comp, SSet.const_comp])

/-- 概要：coslice の fiber の射影を元へ含めると元の終点射影。
方針：fiber への持ち上げの定義を計算する。
規約：全次数で厳密な等式。
使われ方：Kerodon §5.1.1 の相対充填の比較。 -/
lemma cosliceFiberProjection_ι {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (s : (sliceUnder (a ≫ p)) _⦋0⦌) :
    cosliceFiberProjection a p s ≫
      vertexFiberι p ((sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s) =
        vertexFiberι (sliceUnderPostcomp a p) s ≫ sliceUnderProjection a := rfl

/-- 概要：inner fibration の基底の辺を固定した coslice の射影は left fibration。
方針：相対 coslice の射の持ち上げに定値の基底の辺を指定し、fiber に戻す。
規約：元・標的の quasicategory 性は不要。
使われ方：Kerodon §5.1.1 の輸送による射の空間の比較。 -/
instance cosliceFiberProjection_leftFibration {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [InnerFibration p]
    (s : (sliceUnder (a ≫ p)) _⦋0⦌) : LeftFibration (cosliceFiberProjection a p s) where
  mem := by
    intro A D i hi
    have := LeftFibration.mem (p := cosliceEndpointMap a p) i hi
    constructor
    intro f b sq
    let y := (sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s
    let q := sliceUnderPostcomp a p
    have hbase : (b ≫ vertexFiberι p y) ≫ p =
        (SSet.const s : D ⟶ sliceUnder (a ≫ p)) ≫ sliceUnderProjection (a ≫ p) := by
      rw [Category.assoc, vertexFiberι_comp, SSet.const_comp, SSet.comp_const]
    let T := pullback.lift (b ≫ vertexFiberι p y) (SSet.const s) hbase
    have hw : (f ≫ vertexFiberι q s) ≫ cosliceEndpointMap a p = i ≫ T := by
      apply pullback.hom_ext
      · simp only [Category.assoc, cosliceEndpointMap_fst, T, pullback.lift_fst]
        have hh := congrArg (fun t ↦ t ≫ vertexFiberι p y) sq.w
        rw [Category.assoc, cosliceFiberProjection_ι, ← Category.assoc] at hh
        exact hh
      · simp only [Category.assoc, cosliceEndpointMap_snd, T, pullback.lift_snd]
        change f ≫ vertexFiberι q s ≫ q = i ≫ SSet.const s
        simp only [vertexFiberι_comp, SSet.comp_const]
    let hs : CommSq (f ≫ vertexFiberι q s) i (cosliceEndpointMap a p) T := ⟨hw⟩
    have hfix : hs.lift ≫ q = SSet.const s := by
      have hh := congrArg (fun t ↦ t ≫ pullback.snd p (sliceUnderProjection (a ≫ p))) hs.fac_right
      simp only [Category.assoc, cosliceEndpointMap_snd, T, pullback.lift_snd] at hh
      exact hh
    refine CommSq.HasLift.mk' {
      l := vertexFiberLift q s hs.lift hfix
      fac_left := ?_
      fac_right := ?_ }
    · apply vertexFiber_hom_ext q s
      rw [Category.assoc, vertexFiberLift_ι]
      exact hs.fac_left
    · apply vertexFiber_hom_ext p y
      rw [Category.assoc, cosliceFiberProjection_ι, ← Category.assoc, vertexFiberLift_ι]
      have hh := congrArg (fun t ↦ t ≫ pullback.fst p (sliceUnderProjection (a ≫ p))) hs.fac_right
      simp only [Category.assoc, cosliceEndpointMap_fst, T, pullback.lift_fst] at hh
      exact hh

/-- 概要：cocartesian な辺の始点から fiber の終対象へ向かう固定基底上の射の空間は可縮。
方針：cocartesian な持ち上げが与える始対象と left fibration の終対象上の fiber の充填を使う。
規約：元・標的の quasicategory 性は不要。
使われ方：Kerodon §7.1.5 の fiber の終対象から相対終対象への接続。 -/
lemma cosliceFiberProjection_terminalFiber_isContractibleKan {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [CocartesianHornFibration p]
    (s : (sliceUnder (a ≫ p)) _⦋0⦌)
    (x : (vertexFiber p ((sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s)) _⦋0⦌)
    (hx : IsTerminalVertex x) :
    IsContractibleKan (vertexFiber (cosliceFiberProjection a p s) x) := by
  obtain ⟨t, ht, hp⟩ := exists_cocartesianCosliceVertex_lift a p s
  let t' : (vertexFiber (sliceUnderPostcomp a p) s) _⦋0⦌ := ⟨t, by
    have h0 : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := Subsingleton.elim _ _
    simpa only [PinchedHom.constant, h0, op_id,
      CategoryTheory.Functor.map_id_apply] using hp⟩
  exact leftFibration_terminalFiber_isContractibleKan (cosliceFiberProjection a p s)
    (isInitialVertex_cocartesianCosliceFiber a p s t' ht) hx

end SerrePositivity.InfinityCategories
