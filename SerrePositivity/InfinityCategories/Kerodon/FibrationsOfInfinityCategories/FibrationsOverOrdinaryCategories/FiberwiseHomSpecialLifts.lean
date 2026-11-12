module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.FinalFiberTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseHomLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteTotalFibers

/-!
概要：終点の逆像の図式を cocartesian 辺を可逆にする全逆像上の図式へ延長する。
方針：最終 fiber への retraction の可逆性を、逆像の二つの表示の比較と合成する。
規約：特殊な辺の存在を構成し、その cartesian 性は後続で判定する。
使われ方：Kerodon §5.3.6（Tag 037W） の相対指数の特殊な辺の構成。

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

/-- 概要：最後の頂点の逆像上の図式は cocartesian 辺を可逆にする全逆像の図式へ延長できる。
方針：最終 fiber への可逆化する retraction と pullback の比較を使う。
規約：第二射影による標準の cocartesian fibration 上で可逆化条件を述べる。
使われ方：相対指数の cartesian になるべき辺を実際に構成する。 -/
lemma exists_kanFiberwiseHom_finalVertex_extension_inverting (n : ℕ)
    {K C D : SSet.{u}} [Quasicategory D]
    (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (b : (Δ[n] : SSet.{u}) ⟶ C)
    (H₀ : pullback
      ((SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n)) : (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ b)
      p ⟶ D) :
    ∃ H : pullback b p ⟶ D,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map
        (Over.homMk (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n))) rfl :
          Over.mk ((SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n)) :
            (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ b) ⟶ Over.mk b) ≫ H = H₀ ∧
      ∀ e : (pullback p b) _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.snd p b) e →
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
          (((pullbackSymmetry p b).hom ≫ H).app (Opposite.op ⦋1⦌) e)) := by
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
  obtain ⟨G, hG, hGi⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.exists_kanFinalFiber_extension_inverting n q (e.inv ≫ H₀)
  refine ⟨(pullbackSymmetry b p).hom ≫ G, ?_, ?_⟩
  · change m ≫ (pullbackSymmetry b p).hom ≫ G = H₀
    rw [← Category.assoc, hm, ← he, Category.assoc, hG,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · have hs : (pullbackSymmetry p b).hom ≫ (pullbackSymmetry b p).hom = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]
      · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
          pullbackSymmetry_hom_comp_fst, Category.id_comp]
    have hcomp : (pullbackSymmetry p b).hom ≫ ((pullbackSymmetry b p).hom ≫ G) = G := by
      rw [← Category.assoc, hs, Category.id_comp]
    rw [hcomp]
    exact hGi

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
