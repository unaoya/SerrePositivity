module
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputPrecompComposition
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
/-!
概要：元の unlifted・resolved 比較を、同じ入力 Up と出力 Down による前後合成へ回収する。
方針：既存定義の端点輸送だけを除き、元の指定比較をそのまま保持する。
規約：比較や切断を選び直さない。使われ方：元の resolved 比較の前合成則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (A C : Type (max (u + 1) v w))
  [DGCategory R A] [DGCategory R C] (E : Type w) [DGCategory R E] [Small.{u} E]
/-- 元の unlifted 比較は、同じ指定比較への元の入力 Up の前合成である。 -/
lemma dgModuleOutputResolution_unliftedPrecompIso_heq
    (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E)) :
    HEq (dgModuleOutputResolution_unliftedPrecompIso.{u, v, w} R A C E H F)
      ((dgModuleOutputResolution_precompIso R A C E H F).precomp
        (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A))) := by
  simp only [dgModuleOutputResolution_unliftedPrecompIso,
    Eq.mp, Eq.mpr]
  rfl
/-- 元の resolved 比較は、同じ unlifted 比較への半自由出力 Down の後合成である。 -/
lemma dgModuleResolvedInfinity_precompIso_heq (A C : Type (max (u + 1) v))
    [DGCategory R A] [DGCategory R C]
    (E : Type v) [DGCategory R E] [Small.{u} E]
    (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E)) :
    HEq (dgModuleResolvedInfinity_precompIso R A C E H F)
      ((dgModuleOutputResolution_unliftedPrecompIso.{u, v, v} R A C E H F).postcomp
        (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
          (SemifreeDGModules R E)))) := by
  simp only [dgModuleResolvedInfinity_precompIso, Eq.mp]
  rfl
end SerrePositivity.InfinityCategories
