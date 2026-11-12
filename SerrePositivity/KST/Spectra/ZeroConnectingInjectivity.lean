module

public import SerrePositivity.KST.Spectra.BoundaryFilling
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSequence

/-!
概要：全境界充填を持つ全空間の零次数への連結写像の単射性。
方針：二つの持ち上げと fiber 内の辺を三角形の境界へ貼り、全空間で充填する。
規約：π₁ の核の自明性だけに頼らず、類の等式を幾何的に構成する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。π₀(ΩY) と π₁(Y) の比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

namespace ZeroConnectingTriangle

variable {E B : SSet.{u}} {p : E ⟶ B} {e : E _⦋0⦌}
  {s t : B.PtSimplex 1 (p.app _ e)} (Ls : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) (Lt : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e t)
  (r : PtSimplex.RelStruct₀ Ls.boundary Lt.boundary)

/-- 概要：二つの持ち上げと fiber 内の辺を三角形の面に置く。
方針：頂点二を全空間の基点とし、面二に fiber 内の辺を置く。
規約：面零が Ls、面一が Lt。
使われ方：Goerss–Jardine I §7。連結写像の零次数の単射性。 -/
def face : Fin 3 → ((Δ[1] : SSet.{u}) ⟶ E) :=
  ![Ls.map, Lt.map, r.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)]

/-- 概要：三角形の三つの面は端点で互換。
方針：持ち上げの基点条件と fiber 内の辺の端点条件を使う。
規約：三組の端点を直接検査する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。全境界充填への入力。 -/
theorem compatible : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.IsCompatible (face Ls Lt r) := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;> try (simp at hjk)
  · change stdSimplex.δ (0 : Fin 2) ≫ Ls.map = stdSimplex.δ (0 : Fin 2) ≫ Lt.map
    rw [Ls.face_eq 0 (by decide), Lt.face_eq 0 (by decide)]
  · change stdSimplex.δ (1 : Fin 2) ≫ Ls.map =
      (stdSimplex.δ (0 : Fin 1).castSucc ≫ r.map) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)
    rw [r.δ_castSucc_map]
    exact Ls.boundary_ι.symm
  · change stdSimplex.δ (1 : Fin 2) ≫ Lt.map =
      (stdSimplex.δ (0 : Fin 1).succ ≫ r.map) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)
    rw [r.δ_succ_map]
    exact Lt.boundary_ι.symm

include Ls Lt r in
/-- 概要：全空間の三角形の全境界充填から底の二つのループの類の等式を得る。
方針：充填を底へ射影し、fiber 内の辺が定数となることを使う。
規約：底は Kan、全空間の終対象への射に単射の RLP を仮定する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。零次数の連結射の単射性。 -/
theorem class_eq [KanComplex B]
    (hE : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk t := by
  obtain ⟨q, hq⟩ := BoundaryFaces.exists_filler hE (compatible Ls Lt r)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound (i := (0 : Fin 2))
  refine ⟨q ≫ p, ?_, ?_, ?_, ?_⟩
  · change stdSimplex.δ (0 : Fin 3) ≫ (q ≫ p) = s.map
    rw [← Category.assoc, hq]
    exact Ls.map_comp
  · change stdSimplex.δ (1 : Fin 3) ≫ (q ≫ p) = t.map
    rw [← Category.assoc, hq]
    exact Lt.map_comp
  · intro j hj
    exact (not_lt_of_ge (Fin.zero_le j) hj).elim
  · intro j hj
    have hj2 : j = 2 := by fin_cases j <;> simp_all
    subst j
    rw [← Category.assoc, hq]
    change (r.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) ≫ p = SSet.const (p.app _ e)
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp, SSet.comp_const]

end ZeroConnectingTriangle

/-- 概要：全境界充填を持つ全空間の π₁(B) から π₀(fiber) への連結写像は単射。
方針：fiber の二頂点の類の等式を辺で表し、持ち上げとともに全三角形を充填する。
規約：全空間から終対象への射の全ての単射への RLP を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の零次数の比較。 -/
theorem connecting_zero_injective {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌)
    (hE : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E)) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e 0) := by
  intro a b h
  induction a using Quotient.inductionOn with | h s => ?_
  induction b using Quotient.inductionOn with | h t => ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk t) at h
  let Ls := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e s
  let Lt := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e t
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e Ls, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e Lt] at h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk Ls.boundary = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk Lt.boundary at h
  obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopyZero.mk_eq_iff Ls.boundary Lt.boundary).1 h
  exact ZeroConnectingTriangle.class_eq Ls Lt r hE

end

end SerrePositivity.KST.Spectra
