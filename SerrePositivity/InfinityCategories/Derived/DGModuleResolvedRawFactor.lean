module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
/-!
概要：実出力分解を全加群の同じ恒等関手の出力分解へ因数分解する。
方針：元の指定切断・augmentation と、全単体上の関手比較を使う。
規約：元の入力 Hom の平坦性・出力の射影性を仮定しない。
使われ方：一般 kernel の導来合成とその模型移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
/-- 元の実出力分解は、元の nerve と恒等関手の実出力分解の合成に全関手同型。 -/
def dgModuleResolvedInfinity_rawFactorIso (F : DGFunctor R C (RightModule R E)) :
    FunctorIso (dgModuleResolvedInfinity R C E F)
      (dgNerve.map F ≫ dgModuleResolvedInfinity R (RightModule R E) E
        (DGFunctor.id (RightModule R E))) := by
  have hf : F.comp (DGFunctor.id (RightModule R E)) = F := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro x y
    simp only [EnrichedFunctor.comp_map, EnrichedFunctor.id_map,
      eqToHom_refl, Category.comp_id]
  have e := dgModuleResolvedInfinity_precompIso R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))
  rw [hf] at e
  exact e
/-- 元の全関手同型を、同じ半自由出力分解の全関手同型へ送る。 -/
def dgModuleResolvedInfinity_isoOfRawFunctorIso
    (F G : DGFunctor R C (RightModule R E))
    (e : FunctorIso (dgNerve.map F) (dgNerve.map G)) :
    FunctorIso (dgModuleResolvedInfinity R C E F) (dgModuleResolvedInfinity R C E G) :=
  dgModuleResolvedInfinity_rawFactorIso R C E F ≪≫
    e.postcomp (dgModuleResolvedInfinity R (RightModule R E) E
      (DGFunctor.id (RightModule R E))) ≪≫
    (dgModuleResolvedInfinity_rawFactorIso R C E G).symm
end SerrePositivity.InfinityCategories
