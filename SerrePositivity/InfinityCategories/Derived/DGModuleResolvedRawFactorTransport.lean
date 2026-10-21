module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactorNaturality
/-!
概要：出力 dg 関手の等しい二表示は、元の指定 raw factor 比較の値を保持する。
方針：同じ dg 関手の等式を消去し、既存の比較そのものを使う。
規約：比較を選び直さない。使われ方：三項経路の両射影による端点輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
/-- 同じ出力 dg 関手の表示の等式は、元の指定 raw factor を型付きで保持する。 -/
lemma dgModuleResolvedInfinity_rawFactorIso_heq_of_output_eq
    {F G : DGFunctor R C (RightModule R E)} (h : F = G) :
    HEq (dgModuleResolvedInfinity_rawFactorIso R C E F)
      (dgModuleResolvedInfinity_rawFactorIso R C E G) := by
  subst G
  rfl
end SerrePositivity.InfinityCategories
