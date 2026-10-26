module
public import SerrePositivity.KST.SConstruction.Cofinality.CokernelNerveMap

/-!
概要：元の余核から群 nerve への比較は各次数で全単射となる。
方針：元の連続辺座標と群 nerve の隣接辺座標を逆元によって比較する。
規約：群 nerve の座標規約の符号を保持する。
使われ方：元の障害余核の単体的な bar 同型。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：余核の元の連続辺は群 nerve の座標では逆元となる。
方針：隣接二端点の制限を元の連続辺包含と照合する。
規約：Sp の GroupNerve.coordinates は隣接射の逆元を取る。
使われ方：bar 比較の次数ごとの全単射性。 -/
lemma cutCokernelNerve_coordinates {X Y : StableModel.{u}} (f : X ⟶ Y)
    (n : ℕ) (a : cutKZeroCokernel n f) (i : Fin n) :
    Spectra.GroupNerve.coordinates (Multiplicative (cutKZeroCokernel 1 f))
        (cutCokernelNerveSimplex f n a) i =
      Multiplicative.ofAdd (-(cutCokernelEdgeEquiv f n a i)) := by
  have he : cokernelIntervalOrder i.castSucc i.succ (Fin.castSucc_le_succ i) =
      edgeIntervalInclusion n i := by
    apply DFunLike.ext
    intro b
    apply Fin.ext
    fin_cases b
    · exact (Nat.add_zero i.val).symm
    · rfl
  change (Multiplicative.ofAdd (cutCokernelRestriction f
    (cokernelIntervalOrder i.castSucc i.succ (Fin.castSucc_le_succ i)) a))⁻¹ = _
  have h := DFunLike.congr_fun (congrArg (cutCokernelRestriction f) he) a
  exact congrArg (fun b => Multiplicative.ofAdd (-b))
    (h.trans (cutCokernelEdgeEquiv_apply f n a i).symm)

/-- 概要：元の余核の bar 比較は各次数で全単射。
方針：既存の二つの辺座標同型の間で逆元を取る。
規約：比較射は構成済みの元の区間値による射。
使われ方：単体的な障害 bar 同型。 -/
lemma cutCokernelNerveSimplex_bijective {X Y : StableModel.{u}} (f : X ⟶ Y) (n : ℕ) :
    Function.Bijective (cutCokernelNerveSimplex f n) := by
  have hb : Function.Bijective (fun a : cutKZeroCokernel n f =>
      fun i : Fin n => Multiplicative.ofAdd (-(cutCokernelEdgeEquiv f n a i))) := by
    constructor
    · intro a b h
      apply (cutCokernelEdgeEquiv f n).injective
      funext i
      exact neg_injective (congrFun h i)
    · intro b
      refine ⟨(cutCokernelEdgeEquiv f n).symm (fun i => -(Multiplicative.toAdd (b i))), ?_⟩
      funext i
      change Multiplicative.ofAdd (-((cutCokernelEdgeEquiv f n)
        ((cutCokernelEdgeEquiv f n).symm (fun i => -(Multiplicative.toAdd (b i))))) i) = b i
      rw [AddEquiv.apply_symm_apply, neg_neg]
      rfl
  have he : (fun a => Spectra.GroupNerve.coordinatesEquiv
      (Multiplicative (cutKZeroCokernel 1 f)) n (cutCokernelNerveSimplex f n a)) =
      (fun a i => Multiplicative.ofAdd (-(cutCokernelEdgeEquiv f n a i))) := by
    funext a i
    exact cutCokernelNerve_coordinates f n a i
  have hc := he.symm ▸ hb
  exact Function.Bijective.of_comp_left hc (Spectra.GroupNerve.coordinatesEquiv
    (Multiplicative (cutKZeroCokernel 1 f)) n).injective

end SerrePositivity.KST.SConstruction.Cofinality
