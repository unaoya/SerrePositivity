module

public import SerrePositivity.AlgebraicGeometry.IdealSheafOpenBaseChange
public import SerrePositivity.AlgebraicGeometry.OpenCenterExtension

/-!
概要：開の重なりで一致する部分イデアル層を、同じ大域イデアルの中で貼る。
方針：既存の準コンパクト開による像と有限共通部分を使う。
規約：有限型性そのものは別の被覆の判定に渡す。
使われ方：Stacks 01PF の有限型部分イデアルの延長。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 開埋め込みへのイデアル層の逆像は二項共通部分を保存する。 -/
theorem idealSheaf_comap_inf_of_openImmersion {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (K L : Y.IdealSheafData) :
    (K ⊓ L).comap j = K.comap j ⊓ L.comap j := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_inf, Pi.inf_apply, Ideal.comap_inf]

set_option backward.isDefEq.respectTransparency false in
/-- 重なりで一致する部分イデアル層を、指定した大域イデアル層の中で貼り合わせる。 -/
theorem exists_subideal_gluing_open_pair
    {W X Y S : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ Y)
    (j : X ⟶ S) (v : Y ⟶ S)
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion v] [QuasiCompact v]
    (h : IsPullback a b j v) (I : S.IdealSheafData)
    (K : X.IdealSheafData) (L : Y.IdealSheafData)
    (hK : K ≤ I.comap j) (hL : L ≤ I.comap v)
    (hcompat : K.comap a = L.comap b) :
    ∃ J : S.IdealSheafData, J ≤ I ∧ J.comap j = K ∧ J.comap v = L := by
  refine ⟨I ⊓ K.map j ⊓ L.map v, inf_le_left.trans inf_le_left, ?_, ?_⟩
  · rw [idealSheaf_comap_inf_of_openImmersion,
      idealSheaf_comap_inf_of_openImmersion,
      idealSheaf_comap_map_openImmersion,
      idealSheaf_comap_map_of_isPullback_openImmersion b a v j h.flip L,
      ← hcompat, inf_eq_right.mpr hK]
    exact inf_eq_left.mpr (K.le_map_comap a)
  · rw [idealSheaf_comap_inf_of_openImmersion,
      idealSheaf_comap_inf_of_openImmersion,
      idealSheaf_comap_map_openImmersion,
      idealSheaf_comap_map_of_isPullback_openImmersion a b j v h K,
      hcompat]
    exact le_antisymm inf_le_right (le_inf hL (L.le_map_comap b) |> fun h' ↦ le_inf h' le_rfl)

end SerrePositivity.AlgebraicGeometry
