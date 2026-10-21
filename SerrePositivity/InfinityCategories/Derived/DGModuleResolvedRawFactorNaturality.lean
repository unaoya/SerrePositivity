module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecompComposition
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactor
/-!
概要：元の指定 raw factor 比較は、任意の dg 入力前合成と整合する。
方針：元の resolved 比較の合成則を恒等出力に適用し、同じ恒等合成の端点を輸送する。
規約：元の比較と実関手を保持する。使われ方：導来 kernel 合成子の経路照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (A B : Type (max (u + 1) v))
  [DGCategory R A] [DGCategory R B] (E : Type v) [DGCategory R E] [Small.{u} E]
omit [DGCategory R A] in
/-- 元の raw factor 比較は、同じ指定前合成比較を恒等出力へ適用した値である。 -/
lemma dgModuleResolvedInfinity_rawFactorIso_heq (F : DGFunctor R B (RightModule R E)) :
    HEq (dgModuleResolvedInfinity_rawFactorIso R B E F)
      (dgModuleResolvedInfinity_precompIso R B (RightModule R E) E F
        (DGFunctor.id (RightModule R E))) := by
  simp only [dgModuleResolvedInfinity_rawFactorIso, Eq.mp]
  rfl
/-- 出力 dg 関手の同じ表示の等式は、元の指定前合成比較を型付きで保持する。 -/
lemma dgModuleResolvedInfinity_precompIso_heq_of_output_eq (H : DGFunctor R A B)
    {F G : DGFunctor R B (RightModule R E)} (h : F = G) :
    HEq (dgModuleResolvedInfinity_precompIso R A B E H F)
      (dgModuleResolvedInfinity_precompIso R A B E H G) := by
  subst G
  rfl
/-- 元の raw factor 比較は、同じ入力 dg 関手の前合成に関して型付きで自然。 -/
lemma dgModuleResolvedInfinity_rawFactorIso_precomp_heq (H : DGFunctor R A B)
    (F : DGFunctor R B (RightModule R E)) :
    HEq (dgModuleResolvedInfinity_rawFactorIso R A E (H.comp F))
      (dgModuleResolvedInfinity_precompIso R A B E H F ≪≫
        (dgModuleResolvedInfinity_rawFactorIso R B E F).precomp (dgNerve.map H)) := by
  let I : DGFunctor R (RightModule R E) (RightModule R E) :=
    DGFunctor.id (RightModule R E)
  have hF : F.comp I = F := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro X Y
    simp only [EnrichedFunctor.comp_map,
      eqToHom_refl, Category.comp_id]
  let p := dgModuleResolvedInfinity_precompIso R A B E H F
  let q := (dgModuleResolvedInfinity_rawFactorIso R B E F).precomp (dgNerve.map H)
  let p' := dgModuleResolvedInfinity_precompIso R A B E H (F.comp I)
  let q' := (dgModuleResolvedInfinity_precompIso R B (RightModule R E) E F I).precomp
    (dgNerve.map H)
  have hp : HEq p p' :=
    (dgModuleResolvedInfinity_precompIso_heq_of_output_eq R A B E H hF).symm
  have hq : HEq q q' :=
    F2.functorIso_precomp_heq_of_heq
      (dgModuleResolvedInfinity_precompIso R B (RightModule R E) E F I)
      (dgModuleResolvedInfinity_rawFactorIso R B E F)
      (congrArg (dgModuleResolvedInfinity R B E) hF) rfl
      (dgModuleResolvedInfinity_rawFactorIso_heq R B E F) (dgNerve.map H)
  have hs := congrArg (fun G => dgModuleResolvedInfinity R A E (H.comp G)) hF.symm
  have ht := congrArg (fun G => dgNerve.map H ≫ dgModuleResolvedInfinity R B E G) hF.symm
  have hpath := functorIso_trans_heq p q p' q' hs ht rfl hp hq
  exact (dgModuleResolvedInfinity_rawFactorIso_heq R A E (H.comp F)).trans
    ((dgModuleResolvedInfinity_precompIso_comp_heq R A B (RightModule R E) E H F I).trans
      hpath.symm)
/-- 明示した元の nerve 合成の端点輸送の下で、raw factor の入力自然性は等式となる。 -/
lemma dgModuleResolvedInfinity_rawFactorIso_precomp (H : DGFunctor R A B)
    (F : DGFunctor R B (RightModule R E)) :
    F2.functorIsoOfEq (dgModuleResolvedInfinity_rawFactorIso R A E (H.comp F)) rfl
      (congrArg (fun m => m ≫ dgModuleResolvedInfinity R (RightModule R E) E
        (DGFunctor.id (RightModule R E))) (dgNerve.map_comp H F)) =
      dgModuleResolvedInfinity_precompIso R A B E H F ≪≫
        (dgModuleResolvedInfinity_rawFactorIso R B E F).precomp (dgNerve.map H) := by
  apply eq_of_heq
  exact (F2.functorIsoOfEq_heq _ _ _).trans
    (dgModuleResolvedInfinity_rawFactorIso_precomp_heq R A B E H F)
end SerrePositivity.InfinityCategories
