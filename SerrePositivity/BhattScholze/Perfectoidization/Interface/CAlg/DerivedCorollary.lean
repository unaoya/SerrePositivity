module

public import SerrePositivity.BhattScholze.Perfectoidization.Interface.CAlg.Definition

/-!
# CAlg_R 版 BS 界面の D(R) 版の系

概要：CAlg_R 界面から既存 G1 界面を構成する。
方針：実 U の任意 coherent 極限保存と完成済みの離散比較を代入する。
規約：D(R) の極限性・excision を追加仮定しない。文献入力の存在は主張しない。
使われ方：既存 G1 の環の普遍性・excision の下流をそのまま使用できる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Perfectoidization
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet
open _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface
open _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
variable {hR : IsIntegralPerfectoid R p}

/-- 概要：同じ指定 BS 錐の底の極限性。
方針：U の極限保存と全錐比較を合成する。規約：形状の制限なし。
使われ方：旧 G1 の limit_isLimit の欄。 -/
lemma BSLimitConeDataCAlg.underlying_isLimit
    {P : algebraNerve R ⟶ CAlg_R R} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (algebraEmbedding R) P}
    {h0 : H0RingData R (P ≫ cAlgForgetDerived R) (underlyingUnit R η)} {S : A_R R}
    (c : BSLimitConeDataCAlg R p P η h0 S) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c.cone) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c.underlying.cone :=
  (cAlgForgetDerived_mapJoinCone_isLimit R c.cone hc).of_functorIso c.comparison

/-- 概要：実 U と指定比較による旧 G1 界面の構成。
方針：離散性は本質像の比較、極限と excision は右随伴 U の保存を使う。
規約：単位・H⁰・指定錐・通常の商・非完備始域を保持する。
使われ方：CAlg_R 版の存在を供給した場合の D(R) 版の系。 -/
def PerfectoidizationInterfaceCAlg.toE3 (F : PerfectoidizationInterfaceCAlg R p hR) :
    PerfectoidizationInterfaceE3 R p hR where
  perfd := F.perfd ≫ cAlgForgetDerived R
  unit := underlyingUnit R F.unit
  h0 := F.h0
  universal S hS := F.universal S ((disc_forget_iff R _).mp hS)
  limitCone S := (F.limitCone S).underlying
  limit_isLimit S := (F.limitCone S).underlying_isLimit R p (F.limit_isLimit S)
  integral S hS := ⟨(disc_forget_iff R _).mpr (F.integral S hS).1, (F.integral S hS).2⟩
  excision f I hS hT hI ha := by
    simpa only [perfdSquare, Category.assoc] using
      forget_pullback R (F.excision f I hS hT hI ha)

/-- 概要：CAlg_R 版の存在から D(R) 版の存在への証明済みの還元。
方針：toE3 を適用する。規約：存在入力や引用は新設しない。
使われ方：既存の文献入力を述べ直す際の下流への橋。 -/
theorem nonempty_e3_of_cAlg (h : Nonempty (PerfectoidizationInterfaceCAlg R p hR)) :
    Nonempty (PerfectoidizationInterfaceE3 R p hR) :=
  h.map (PerfectoidizationInterfaceCAlg.toE3 R p)

end SerrePositivity.EInfinity.Perfectoidization
