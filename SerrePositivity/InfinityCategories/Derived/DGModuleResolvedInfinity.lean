module
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionAugmentation
/-!
概要：共通対象宇宙の任意の dg 加群値関手を、元の実半自由模型へ移す。
方針：実出力分解の前後に対象宇宙だけの上げ下げを合成する。
規約：出力の射影性も入力の小ささも不要。使われ方：一般双加群作用とその比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 実出力分解を、元の入力の dg nerve から元の半自由模型への実 ∞ 関手にする。 -/
def dgModuleResolvedInfinity : dgNerve R C ⟶ dgModuleDerivedInfinityCategory R E :=
  dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
  dgModuleOutputResolutionInfinity R C E F ≫
  dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
    (SemifreeDGModules R E))
end SerrePositivity.InfinityCategories
