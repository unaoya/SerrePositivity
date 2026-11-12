module

public import SerrePositivity.KST.LocalizingInvariants.DGExtensionUnitHomNaturality
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom

/-!
概要：D の元の恒等制限同型の逆を、全 Hom に自然な厳密 dg 自然変換へ移す。
方針：元の逆同型の評価が恒等であることと、制限 Hom の評価公式を使う。
規約：元の制限と同型を保持。使われ方：実 Perf 延長の恒等比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

private lemma homPost_id (K L : Complex R) : homPostcompose K (𝟙 L) = 𝟙 _ :=
  (homFunctor K).map_id L

private lemma homPre_id (K L : Complex R) : homPrecompose (𝟙 K) L = 𝟙 _ := by
  apply chain_ext_apply
  intro n z
  exact CochainComplex.HomComplex.Cochain.id_comp z

lemma dgRestrictionIdentityInvHomNaturality (M N : RightModule R D) :
    moduleHomPostcompose R D M N _
      ((moduleRestrictionIdObjIso R D (ForgetEnrichment.of (Complex R) N)).inv) =
    moduleRestrictionHom R D D (DGFunctor.id D).op M N ≫ moduleHomPrecompose R D _ _ _
      ((moduleRestrictionIdObjIso R D (ForgetEnrichment.of (Complex R) M)).inv) := by
  let c (P : RightModule R D) : ForgetEnrichment.of (Complex R) P ⟶
      ForgetEnrichment.of (Complex R) (restrictModule R D D (DGFunctor.id D).op P) :=
    (moduleRestrictionIdObjIso R D (ForgetEnrichment.of (Complex R) P)).inv
  change moduleHomPostcompose R D M N
      (restrictModule R D D (DGFunctor.id D).op N) (c N) =
    _ ≫ moduleHomPrecompose R D M (restrictModule R D D (DGFunctor.id D).op M)
      (restrictModule R D D (DGFunctor.id D).op N) (c M)
  apply moduleHom_ext
  intro d
  have he (P : RightModule R D) : (moduleEvaluation R D d).map (c P) = 𝟙 _ := by
    have hw := congrArg (fun f => (moduleEvaluation R D d).map f)
      (moduleRestrictionIdObjIso R D (ForgetEnrichment.of (Complex R) P)).hom_inv_id
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleRestrictionIdObjIso_hom_eval, Category.id_comp] at hw
    exact hw
  rw [moduleHomPostcompose_π, Category.assoc _ _ (moduleHomπ R D _ _ d),
    moduleHomPrecompose_π]
  dsimp only [moduleMorphismComponent]
  rw [he, he]
  change moduleHomπ R D M N d ≫ homPostcompose _ (𝟙 _) =
    moduleRestrictionHom R D D (DGFunctor.id D).op M N ≫
      (moduleHomπ R D _ _ d ≫ homPrecompose (𝟙 _) _)
  rw [homPost_id, homPre_id, Category.comp_id, Category.comp_id, moduleRestrictionHom_π]
  rfl

/-- 元の恒等制限の逆同型を成分に持つ、厳密 dg 自然変換。 -/
def dgRestrictionIdentityInvStrict : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (DGFunctor.id (RightModule R D))
    (dgModuleRestriction R D D (DGFunctor.id D).op) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R D
    (fun M => (moduleRestrictionIdObjIso R D (ForgetEnrichment.of (Complex R) M)).inv)
    (fun M N => by
      change 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
      exact dgRestrictionIdentityInvHomNaturality R D M N)

/-- 左関手が恒等である随伴の単位として、同じ元の逆同型を表示する。 -/
def dgRestrictionIdentityUnitStrict : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (DGFunctor.id (RightModule R D))
    ((DGFunctor.id (RightModule R D)).comp (dgModuleRestriction R D D (DGFunctor.id D).op)) where
  app M := (dgRestrictionIdentityInvStrict R D).app M
  naturality f := (dgRestrictionIdentityInvStrict R D).naturality f

end SerrePositivity.KST.LocalizingInvariants
