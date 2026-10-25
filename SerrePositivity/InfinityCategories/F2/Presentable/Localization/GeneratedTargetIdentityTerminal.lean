module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceRetractionSpace
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceTerminalMapping

/-!
概要：固定始域圏の終対象の終域では、恒等射が新たな固定始域圏の終対象になる。
方針：閉包内の任意の辺の retraction 空間の可縮性を、全部分圏の終対象判定に渡す。
規約：終対象の存在を仮定する。局所対象性の一般の写像に関する判定は残る。
使われ方：HTT 5.5.5.14 の局所性を pushout に沿って戻す前の段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 回収した元の脚を再び余錐にすると、元の同じ指定余錐を回収する。 -/
lemma edgeCosliceVertex_generatedSourceLeg
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (t : (generatedSourceCategory edges x) _⦋0⦌) :
    edgeCosliceVertex (generatedSourceLeg edges x t) = t.val := by
  apply Subtype.ext
  change (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm
      (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
        joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫ t.val.val)) = t.val.val
  rw [Equiv.symm_apply_apply, joinMap_id, Category.id_comp, Iso.hom_inv_id_assoc]

/-- 終対象の終域の恒等射は、その終域を始域とする閉包内射圏の終対象。 -/
lemma generatedSourceIdentity_isTerminal_of_source_terminal
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s) :
    IsTerminalVertex (generatedSourceIdentity edges ((generatedSourceTarget edges x).app _ s)) := by
  let y := (generatedSourceTarget edges x).app _ s
  apply (generatedSource_isTerminal_iff_coslice_mapping_contractible edges y
    (generatedSourceIdentity edges y)).mpr
  intro t
  let v := SSet.Edge.ofTruncated (generatedSourceLeg edges y t)
  have h := generatedSource_terminal_retractionSpace_contractible edges x s hs v
    (generatedSourceLeg_mem edges y t)
  change IsContractibleKan (pinchedHom
    (edgeCosliceVertex (generatedSourceLeg edges y t)) (cosliceIdentityCone y)) at h
  rw [edgeCosliceVertex_generatedSourceLeg] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
