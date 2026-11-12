module

public import SerrePositivity.EInfinity.BarrattEccles.Theory
public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.EInfinity.BarrattEccles.Theory.Conservative
public import SerrePositivity.EInfinity.BarrattEccles.Theory.NativeCoproduct
public import SerrePositivity.EInfinity.BarrattEccles.Theory.DiscreteInitial
public import SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedRestriction
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgDerivedAdjunction
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgExtensionForgetKFlat
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgRestrictionForget
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgRestrictionCoherence
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgDiscreteRestriction
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgPiZeroDiscrete
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgPiZeroRestriction
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCdga

/-!
# Barratt–Eccles の全界面の条件付き組み立て

概要：HA §3.2.2–3.2.4・DAG XIII Construction 2.2.6 の界面の既証明欄を固定する。
方針：保存的な忘却・余積錐・係数変更・π₀・厳密 cdga の比較を既存の証明で供給する。
規約：未供給のテンソル比較と二脚・sifted・Tot・presentable・スペクトル忘却と比較・冪作用だけを引数に取る。
使われ方：BS-W16 段 4。全欄が無条件に構成済みという主張にはしない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.InfinityCategories
attribute [local instance] HasDerivedCategory.standard

/-- 証明済みの欄を固定し、残りの二十一欄だけから全 EInfinityTheory を組み立てる。
同じ全関手版のテンソル同型を、二脚の適合条件の型にも使う。 -/
def barrattEcclesTheoryOfRemaining :=
  fun forget_preservesSifted presentable coproduct_tensor coproduct_tensor_legs
    ofCosimplicial ofCosimplicial_forget ofCosimplicial_cone ofCosimplicial_restrict
    ofCosimplicialCdga ofCosimplicialCdga_cone ofCosimplicialCdga_discrete
    ofCosimplicialCdga_evalZero ofCosimplicialCdga_evalZero_leg
    toSpectra toSpectra_restrict toSpectra_homologyIso powerOp0 powerOp0_zero powerOp0_pos powerOp0_discrete powerOp0_tot =>
  ({ toEInfinityCore := barrattEcclesCore
     forget_conservative := @cAlgForgetDerived_conservative
     forget_preservesSifted := forget_preservesSifted
     presentable := presentable
     coprodWith := @barrattEcclesCoprodWith
     coprodWith_cocone := @barrattEcclesCoprodWith_cocone
     coproduct_tensor := coproduct_tensor
     discrete_initial := @discreteCAlgUnderEmbedding_initial
     coproduct_tensor_legs := coproduct_tensor_legs
     restrictD := @ComplexLimits.barrattEcclesRestrictD
     restrictD_id := @ComplexLimits.barrattEcclesRestrictD_id
     restrictD_comp := @ComplexLimits.barrattEcclesRestrictD_comp
     restrictD_homologyIso := @ComplexLimits.barrattEcclesRestrictD_homologyIso
     restrict := @barrattEcclesRestrict
     baseChange := @barrattEcclesBaseChange
     baseChange_adjunction := @barrattEcclesBaseChange_adjunction
     restrict_forget := @barrattEcclesRestrict_forget
     baseChange_forget := @barrattEcclesBaseChange_forget
     restrict_id := @barrattEcclesRestrict_id
     restrict_comp := @barrattEcclesRestrict_comp
     discrete_restrict := @barrattEcclesDiscrete_restrict
     pi0 := @barrattEcclesPi0
     pi0_forget := @barrattEcclesPi0_forget
     pi0_discrete := @barrattEcclesPi0_discrete
     pi0_restrict := @barrattEcclesPi0_restrict
     strictToD := @ComplexLimits.complexOrdinaryDerivedSource
     strictToD_homologyIso := @ComplexLimits.complexOrdinaryDerivedSourceHomologyIso
     ofCosimplicial := ofCosimplicial
     ofCosimplicial_forget := ofCosimplicial_forget
     ofCosimplicial_cone := ofCosimplicial_cone
     ofCosimplicial_restrict := ofCosimplicial_restrict
     ofCdga := @barrattEcclesOfCdga
     ofCdga_forget := @barrattEcclesOfCdga_forget
     ofCdga_discrete := @barrattEcclesOfCdga_discrete
     ofCosimplicialCdga := ofCosimplicialCdga
     ofCosimplicialCdga_cone := ofCosimplicialCdga_cone
     ofCosimplicialCdga_discrete := ofCosimplicialCdga_discrete
     ofCosimplicialCdga_evalZero := ofCosimplicialCdga_evalZero
     ofCosimplicialCdga_evalZero_leg := ofCosimplicialCdga_evalZero_leg
     toSpectra := toSpectra
     toSpectra_restrict := toSpectra_restrict
     toSpectra_homologyIso := toSpectra_homologyIso
     powerOp0 := powerOp0
     powerOp0_zero := powerOp0_zero
     powerOp0_pos := powerOp0_pos
     powerOp0_discrete := powerOp0_discrete
     powerOp0_tot := powerOp0_tot } : EInfinityTheory.{u})

end SerrePositivity.EInfinity.BarrattEccles
