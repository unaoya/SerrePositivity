module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FinalFiberRetraction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseHomLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteTotalFibers

/-!
概要：相対指数の射影では、標準単体の最後の頂点を指定した持ち上げが存在する。
方針：底変換した cocartesian fibration の最終 fiber へ retract し、図式を延長する。
規約：持ち上げの存在のみを主張し、辺の cartesian 性は別に証明する必要がある。
使われ方：Kerodon §5.3.6（Tag 037W） の相対指数の cartesian な辺の構成の存在部分。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：最後の頂点の逆像上の図式は標準単体の全逆像へ厳密に延長できる。
方針：二つの向きの pullback を比較し、最終 fiber の retraction で図式を延長する。
規約：p は cocartesian fibration、値域 D の充填性は不要。
使われ方：相対指数の終点を指定した持ち上げの存在。 -/
lemma exists_kanFiberwiseHom_finalVertex_extension (n : ℕ) {K C D : SSet.{u}}
    (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (b : (Δ[n] : SSet.{u}) ⟶ C)
    (H₀ : pullback
      ((SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n)) : (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ b)
      p ⟶ D) :
    ∃ H : pullback b p ⟶ D,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map
        (Over.homMk (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n))) rfl :
          Over.mk ((SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n)) :
            (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ b) ⟶ Over.mk b) ≫ H = H₀ := by
  let c := stdSimplex.obj₀Equiv.symm (Fin.last n)
  let j : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.const c
  let u : Over.mk (j ≫ b) ⟶ Over.mk b := Over.homMk j rfl
  let m := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map u
  let q := pullback.snd p b
  let t : pullback (j ≫ b) p ⟶ pullback p b :=
    pullback.lift (pullback.snd (j ≫ b) p) (pullback.fst (j ≫ b) p ≫ j)
      (by rw [Category.assoc]; exact pullback.condition.symm)
  have ht : IsPullback t (pullback.fst (j ≫ b) p) q j := by
    have houter : IsPullback (t ≫ pullback.fst p b) (pullback.fst (j ≫ b) p) p (j ≫ b) := by
      dsimp only [t]
      rw [pullback.lift_fst]
      exact (IsPullback.of_hasPullback (j ≫ b) p).flip
    exact houter.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p b)
  let e : pullback (j ≫ b) p ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q c :=
    ht.isoPullback ≪≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiber_isPullback q c).isoPullback.symm
  have he : e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q c = t := by
    dsimp only [e]
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_hom_fst]
  have hm : m ≫ (pullbackSymmetry b p).hom = t := by
    have hfst := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_fst p u
    have hsnd := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_snd p u
    change m ≫ pullback.fst b p = pullback.fst (j ≫ b) p ≫ j at hfst
    change m ≫ pullback.snd b p = pullback.snd (j ≫ b) p at hsnd
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, hsnd]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, hfst]
      exact (pullback.lift_snd _ _ _).symm
  obtain ⟨G, hG⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanFinalFiber_extension n q (e.inv ≫ H₀)
  refine ⟨(pullbackSymmetry b p).hom ≫ G, ?_⟩
  change m ≫ (pullbackSymmetry b p).hom ≫ G = H₀
  rw [← Category.assoc, hm, ← he, Category.assoc, hG,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- 概要：相対指数の射影は標準単体の最後の頂点に対する右持ち上げ性を持つ。
方針：逆像の最終 fiber 上の図式の延長を、射影の持ち上げへ戻す。
規約：cartesian 性や inner fibration 性は結論に含めない。
使われ方：終点を指定した辺と高次の族の構成の存在部分。 -/
lemma fiberwiseHomProjection_hasLiftingProperty_lastVertex (n : ℕ)
    {K C : SSet.{u}} (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (D : SSet.{u}) :
    HasLiftingProperty
      (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n)) : (Δ[0] : SSet.{u}) ⟶ Δ[n])
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) := by
  constructor
  intro a b sq
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHom_hasLift_iff p sq).2
  exact exists_kanFiberwiseHom_finalVertex_extension n p b _

/-- 概要：相対指数の射影は終点を指定して任意の基底の辺を持ち上げる。
方針：一次元の最後の頂点に対する右持ち上げ性を使う。
規約：持ち上げた辺の cartesian 性は別の判定定理を必要とする。
使われ方：cartesian fibration の辺の存在条件への接続。 -/
lemma fiberwiseHomProjection_hasLiftingProperty_target
    {K C : SSet.{u}} (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (D : SSet.{u}) :
    HasLiftingProperty (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) := by
  rw [stdSimplex.δ_zero_eq_const]
  exact fiberwiseHomProjection_hasLiftingProperty_lastVertex 1 p D

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
