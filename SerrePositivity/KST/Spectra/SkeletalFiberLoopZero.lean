module

public import SerrePositivity.KST.Spectra.SkeletalZeroComponents
public import SerrePositivity.KST.Spectra.SimplexCellZeroLoop

/-!
概要：通常の零 loop の骨格 fiber 比較を既存の成分係数と照合する。
方針：セル表示の厳密な交換式と loop 同値の自然性を使い、セル球面の逆元公式を適用する。
規約：零 loop 比較に伴う逆元を各係数で保持する。
使われ方：Goerss–Jardine VIII §1。成分の障害と実際の群の微分の符号の接続。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 零次数と成分の同値の逆は点つき射に自然。 -/
lemma pointedHomotopyZero_symm_natural {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (f : X ⟶ Y) (a : π₀ X.right) :
    KanHomotopyZero.equivPiZero.symm (mapπ₀ f.right a) =
      pointedHomotopyMap 0 f (KanHomotopyZero.equivPiZero.symm a) := by
  apply KanHomotopyZero.equivPiZero.injective
  rw [Equiv.apply_symm_apply]
  have h := KanHomotopyZero.equivPiZero_map f.right (OmegaSpectrum.pointedMap_basepoint f)
    (KanHomotopyZero.equivPiZero.symm a)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- 零 loop 同値は任意の点つき Kan 射と可換。 -/
lemma loopZeroHomotopyEquiv_pointed_natural {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (f : X ⟶ Y)
    (a : KanHomotopy (loopSpace X).right 0 (loopSpace X).basepoint) :
    loopZeroHomotopyEquiv Y (pointedHomotopyMap 0
        (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} f) a) =
      pointedGroupMap 0 f (loopZeroHomotopyEquiv X a) :=
  loopHomotopyEquiv_natural f 0 a

namespace SkeletalCellAttachment

/-- 概要：零 loop の骨格 fiber 同値は、セル商の写像空間の零 loop 同値から得られる。
方針：セル表示の逆の交換式を零次数へ送り、成分同値と loop 同値の自然性を使う。
規約：厳密な fiber 同型と既存セル表示をそのまま使う。
使われ方：Goerss–Jardine VIII §1。セル係数による零 loop 比較。 -/
lemma stageFiberLoopZeroEquiv_cell (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ)
    (a : KanHomotopy (UnbasedPointedMapping.stageFiber K (loopSpace Y) n).right 0
      (UnbasedPointedMapping.stageFiber K (loopSpace Y) n).basepoint) :
    stageFiberLoopZeroEquiv K Y n a =
      pointedGroupMap 0 (stageFiberCellIso K Y n).hom
        (PointedMapping.loopZeroComponentEquiv (cellCofiber K (n + 1)) Y
          (mapπ₀ (stageFiberCellIso K (loopSpace Y) n).inv.right
            (KanHomotopyZero.equivPiZero a))) := by
  rw [PointedMapping.loopZeroComponentEquiv_apply,
    pointedHomotopyZero_symm_natural, pointedHomotopyZero_symm_natural,
    Equiv.symm_apply_apply]
  have hm : (stageFiberCellIso K (loopSpace Y) n).inv ≫
      (PointedMapping.loopSwap (cellCofiber K (n + 1)) Y).inv ≫
        PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (stageFiberCellIso K Y n).hom =
      (stageFiberLoopIso K Y n).inv := by
    rw [stageFiberLoopIso_cell_inv, Iso.inv_hom_id_assoc]
  have hg := congrArg (fun f ↦ pointedHomotopyMap 0 f a) hm
  simp only [pointedHomotopyMap_comp] at hg
  rw [stageFiberLoopZeroEquiv_apply, ← hg, loopZeroHomotopyEquiv_pointed_natural]

/-- 概要：通常の零 loop の骨格 fiber 比較の各係数は、成分係数を loop で移した値の逆元。
方針：セル表示へ戻し、セル球面への制限の自然性と基本段の逆元公式を使う。
規約：任意の成分の全ての非退化セルについて値を計算する。
使われ方：Goerss–Jardine VIII §1。成分微分と係数微分の符号の照合。 -/
theorem stageFiberCoefficientEquiv_loopZero (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ)
    (a : π₀ (UnbasedPointedMapping.stageFiber K (loopSpace Y) n).right)
    (s : K.nonDegenerate (n + 1)) :
    stageFiberCoefficientEquiv K Y n 0 (stageFiberOrdinaryLoopComponentEquiv K Y n a) s =
      (loopPositiveHomotopyEquiv Y n (stageFiberComponentEquiv K (loopSpace Y) n a s))⁻¹ := by
  change stageFiberCoefficientEquiv K Y n 0
    (stageFiberLoopZeroEquiv K Y n (KanHomotopyZero.equivPiZero.symm a)) s = _
  rw [stageFiberLoopZeroEquiv_cell, Equiv.apply_symm_apply,
    stageFiberCoefficientEquiv_restriction,
    ← pointedGroupMap_comp 0 (stageFiberCellIso K Y n).hom (stageFiberCellIso K Y n).inv,
    Iso.hom_inv_id, pointedGroupMap_id, ← PointedMapping.loopZeroComponentEquiv_pre,
    SimplexCell.positiveHomotopyEquiv_loopZero, stageFiberComponentEquiv_restriction]

end SkeletalCellAttachment
end
end SerrePositivity.KST.Spectra
