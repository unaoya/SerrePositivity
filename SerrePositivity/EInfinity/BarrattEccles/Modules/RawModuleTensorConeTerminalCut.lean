module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConePenultimateValue
public import SerrePositivity.EInfinity.ComplexLimits.ConeFirstBoundary

/-!
概要：実 cone の最後の切断を、元の普遍 cochain の終端削除成分へ同定する。
方針：最後の切断の実評価と、始点回収後の左集合の厳密な一致を使う。
規約：同じ切断・符号・次数を保つ。使われ方：混合 HA の全線形右辺の復元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_terminal_cut_component {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) (ha0 : a = 0)
    (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I)
    (hJ : ((withoutFirst I).erase (Fin.last n)).Nonempty)
    (hkJ : k + 1 = 1 - (((withoutFirst I).erase (Fin.last n)).card : ℤ)) :
    HEq ((strictRawModuleTensorConeData A X P Q c).cutCompose I a b k (penultimate I hI))
      ((k + 1).negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        ((withoutFirst I).erase (Fin.last n)) (k + 1) hJ hkJ) := by
  have h := strictRawModuleTensorConeData_cutCompose_penultimate_value A X P Q c I a b k
    hI ha hb hk hc ha0 hbl h0
  have ht : ∀ (K K' : Finset (Fin (n + 1))) (he : K = K')
      (hK : K.Nonempty) (hK' : K'.Nonempty)
      (hd : k + 1 = 1 - (K.card : ℤ)) (hd' : k + 1 = 1 - (K'.card : ℤ)),
      (strictRawModuleTensorElementLinear A X P Q c).val.component K (k + 1) hK hd =
        (strictRawModuleTensorElementLinear A X P Q c).val.component K' (k + 1) hK' hd' := by
    intro K K' he hK hK' hd hd'
    subst K'
    rfl
  exact h.trans (heq_of_eq (congrArg (fun v => (k + 1).negOnePow • v)
    (ht _ _ (withoutFirst_left_penultimate_last I hI (hb.symm.trans hbl)) _ hJ _ hkJ)))

end SerrePositivity.EInfinity.BarrattEccles
