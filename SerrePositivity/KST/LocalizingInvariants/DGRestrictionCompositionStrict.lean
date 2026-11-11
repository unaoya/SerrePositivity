module

public import SerrePositivity.KST.LocalizingInvariants.DGExtensionUnitHomNaturality
public import SerrePositivity.DifferentialGraded.Verdier.Derived

/-!
概要：D の元の graph 制限の合成同型を全 Hom に自然な厳密 dg 比較へ上げる。
方針：元の同型の評価成分が恒等であることと、制限 Hom の評価公式を使う。
規約：元の加群同型を保持。使われ方：延長の合成比較で右随伴を同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R]

private lemma homPost_id (K L : Complex R) : homPostcompose K (𝟙 L) = 𝟙 _ :=
  (homFunctor K).map_id L

private lemma homPre_id (K L : Complex R) : homPrecompose (𝟙 K) L = 𝟙 _ := by
  apply chain_ext_apply
  intro n z
  exact CochainComplex.HomComplex.Cochain.id_comp z

variable (D E T : Type v) [DGCategory R D] [Small.{u} D]
  [DGCategory R E] [Small.{u} E] [DGCategory R T] [Small.{u} T]
  (F : DGFunctor R D E) (G : DGFunctor R E T)

lemma dgRestrictionCompositionHomNaturality (M N : RightModule R T) :
    (moduleRestrictionHom R E T G.op M N ≫ moduleRestrictionHom R D E F.op _ _) ≫
      moduleHomPostcompose R D _ _ _
        ((graphRestrictionCompositionIso R D E T F G).hom.app
          (ForgetEnrichment.of (Complex R) N)) =
    moduleRestrictionHom R D T (F.comp G).op M N ≫ moduleHomPrecompose R D _ _ _
      ((graphRestrictionCompositionIso R D E T F G).hom.app
        (ForgetEnrichment.of (Complex R) M)) := by
  let c (P : RightModule R T) :
      ForgetEnrichment.of (Complex R) (restrictModule R D E F.op (restrictModule R E T G.op P)) ⟶
      ForgetEnrichment.of (Complex R) (restrictModule R D T (F.comp G).op P) :=
    (graphRestrictionCompositionIso R D E T F G).hom.app (ForgetEnrichment.of (Complex R) P)
  change (_ ≫ _) ≫ moduleHomPostcompose R D
      (restrictModule R D E F.op (restrictModule R E T G.op M))
      (restrictModule R D E F.op (restrictModule R E T G.op N))
      (restrictModule R D T (F.comp G).op N) (c N) =
    _ ≫ moduleHomPrecompose R D
      (restrictModule R D E F.op (restrictModule R E T G.op M))
      (restrictModule R D T (F.comp G).op M) (restrictModule R D T (F.comp G).op N) (c M)
  apply moduleHom_ext
  intro d
  have he (P : RightModule R T) : (moduleEvaluation R D d).map (c P) = 𝟙 _ :=
    moduleIsoMk_hom_eval R D _ _ d
  rw [Category.assoc _ _ (moduleHomπ R D _ _ d), moduleHomPostcompose_π,
    Category.assoc _ _ (moduleHomπ R D _ _ d), moduleHomPrecompose_π]
  dsimp only [moduleMorphismComponent]
  rw [he, he]
  change (moduleRestrictionHom R E T G.op M N ≫ moduleRestrictionHom R D E F.op _ _) ≫
      (moduleHomπ R D _ _ d ≫ homPostcompose _ (𝟙 _)) =
    moduleRestrictionHom R D T (F.comp G).op M N ≫
      (moduleHomπ R D _ _ d ≫ homPrecompose (𝟙 _) _)
  rw [homPost_id, homPre_id, Category.comp_id, Category.comp_id, Category.assoc,
    moduleRestrictionHom_π, moduleRestrictionHom_π, moduleRestrictionHom_π]
  rfl

/-- 元の制限の合成同型と同じ閉零成分を持つ厳密 dg 自然変換。 -/
def dgRestrictionCompositionStrict : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
    ((dgModuleRestriction R E T G.op).comp (dgModuleRestriction R D E F.op))
    (dgModuleRestriction R D T (F.comp G).op) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R D
    (fun M => (graphRestrictionCompositionIso R D E T F G).hom.app
      (ForgetEnrichment.of (Complex R) M))
    (dgRestrictionCompositionHomNaturality R D E T F G)

lemma dgRestrictionCompositionInvHomNaturality (M N : RightModule R T) :
    moduleRestrictionHom R D T (F.comp G).op M N ≫ moduleHomPostcompose R D _ _ _
      ((graphRestrictionCompositionIso R D E T F G).inv.app
        (ForgetEnrichment.of (Complex R) N)) =
    (moduleRestrictionHom R E T G.op M N ≫ moduleRestrictionHom R D E F.op _ _) ≫
      moduleHomPrecompose R D _ _ _
        ((graphRestrictionCompositionIso R D E T F G).inv.app
          (ForgetEnrichment.of (Complex R) M)) := by
  let c (P : RightModule R T) :
      ForgetEnrichment.of (Complex R) (restrictModule R D T (F.comp G).op P) ⟶
      ForgetEnrichment.of (Complex R) (restrictModule R D E F.op (restrictModule R E T G.op P)) :=
    (graphRestrictionCompositionIso R D E T F G).inv.app (ForgetEnrichment.of (Complex R) P)
  change _ ≫ moduleHomPostcompose R D
      (restrictModule R D T (F.comp G).op M) (restrictModule R D T (F.comp G).op N)
      (restrictModule R D E F.op (restrictModule R E T G.op N)) (c N) =
    (_ ≫ _) ≫ moduleHomPrecompose R D
      (restrictModule R D T (F.comp G).op M)
      (restrictModule R D E F.op (restrictModule R E T G.op M))
      (restrictModule R D E F.op (restrictModule R E T G.op N)) (c M)
  apply moduleHom_ext
  intro d
  have he (P : RightModule R T) : (moduleEvaluation R D d).map (c P) = 𝟙 _ := by
    have hh : (moduleEvaluation R D d).map
        ((graphRestrictionCompositionIso R D E T F G).hom.app
          (ForgetEnrichment.of (Complex R) P)) = 𝟙 _ := moduleIsoMk_hom_eval R D _ _ d
    have hw := congrArg (fun f => (moduleEvaluation R D d).map f)
      ((graphRestrictionCompositionIso R D E T F G).app
        (ForgetEnrichment.of (Complex R) P)).hom_inv_id
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Iso.app_hom, hh, Category.id_comp] at hw
    exact hw
  rw [Category.assoc _ _ (moduleHomπ R D _ _ d), moduleHomPostcompose_π,
    Category.assoc _ _ (moduleHomπ R D _ _ d), moduleHomPrecompose_π]
  dsimp only [moduleMorphismComponent]
  rw [he, he]
  change moduleRestrictionHom R D T (F.comp G).op M N ≫
      (moduleHomπ R D _ _ d ≫ homPostcompose _ (𝟙 _)) =
    (moduleRestrictionHom R E T G.op M N ≫ moduleRestrictionHom R D E F.op _ _) ≫
      (moduleHomπ R D _ _ d ≫ homPrecompose (𝟙 _) _)
  rw [homPost_id, homPre_id, Category.comp_id, Category.comp_id, Category.assoc,
    moduleRestrictionHom_π, moduleRestrictionHom_π, moduleRestrictionHom_π]
  rfl

/-- 元の逆同型と同じ成分を持つ、制限の合成比較の厳密逆変換。 -/
def dgRestrictionCompositionInvStrict : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
    (dgModuleRestriction R D T (F.comp G).op)
    ((dgModuleRestriction R E T G.op).comp (dgModuleRestriction R D E F.op)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R D
    (fun M => (graphRestrictionCompositionIso R D E T F G).inv.app
      (ForgetEnrichment.of (Complex R) M))
    (dgRestrictionCompositionInvHomNaturality R D E T F G)

end SerrePositivity.KST.LocalizingInvariants
