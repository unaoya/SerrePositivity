module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactorNaturality
/-!
概要：元の resolved 前合成の合成則を、明示した nerve 合成の端点輸送の下で等式にする。
方針：同じ型付き一致の両端だけを輸送する。
規約：元の指定比較を変更しない。使われ方：指定合成子内の前合成比較の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (A B C : Type (max (u + 1) v))
  [DGCategory R A] [DGCategory R B] [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
/-- 元の二段前合成則は、同じ nerve 合成の端点輸送を明示すれば等式になる。 -/
lemma dgModuleResolvedInfinity_precompIso_comp (H : DGFunctor R A B) (J : DGFunctor R B C)
    (F : DGFunctor R C (RightModule R E)) :
    F2.functorIsoOfEq (dgModuleResolvedInfinity_precompIso R A C E (H.comp J) F) rfl
      (congrArg (fun m => m ≫ dgModuleResolvedInfinity R C E F) (dgNerve.map_comp H J)) =
      dgModuleResolvedInfinity_precompIso R A B E H (J.comp F) ≪≫
        (dgModuleResolvedInfinity_precompIso R B C E J F).precomp (dgNerve.map H) := by
  exact eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
    (dgModuleResolvedInfinity_precompIso_comp_heq R A B C E H J F))
end SerrePositivity.InfinityCategories
