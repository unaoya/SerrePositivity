module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleIdentityResolutionPostcompSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolutionPrecompFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolutionChangeFunctor
/-!
概要：単位からの実射と全 Hom の自然性を、同じ厳密 dg 比較へ接続する。
方針：元の斉次合成と実分解の三成分の等式を使う。
規約：出力の射影性と入力の Small 性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
  (F G : DGFunctor R C (RightModule R E))
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (hs : ∀ x, moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, moduleQuasiIso R E (a x))
  (ha : ∀ x y, (F.comp (DGFunctor.id (RightModule R E))).map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
    (G.comp (DGFunctor.id (RightModule R E))).map x y ≫
      eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id (RightModule R E))))
lemma dgModuleResolutionPrecompChange_hom_square :
    let X₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) X
    let Y₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) Y
    let X₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E
      (F := F.comp (DGFunctor.id (RightModule R E)))
      (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq X
    let Y₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E
      (F := F.comp (DGFunctor.id (RightModule R E)))
      (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq Y
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompAction R E X₀ Y₀ (G.obj Y.source)
          (a Y.source) (hs Y.source) (hq Y.source) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E
      (F := F.comp (DGFunctor.id (RightModule R E)))
      (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R C (RightModule R E) E G
          (DGFunctor.id (RightModule R E)) X₁ Y₁) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPrecompAction R E X₀
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E Y₀ (G.obj Y.source)
            (a Y.source) (hs Y.source) (hq Y.source))
          (G.obj X.source) (a X.source) (hs X.source) (hq X.source) := by
  dsimp only
  let X₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) X
  let Y₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) Y
  let X₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq X
  let Y₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq Y
  let p := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) X Y
  let q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha X Y
  let r := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)) X₁ Y₁
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R C E
    (F.comp (DGFunctor.id (RightModule R E))) X Y
  let t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R C E
    (G.comp (DGFunctor.id (RightModule R E))) X₁ Y₁
  let s₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
    (DGFunctor.id (RightModule R E)) X₀ Y₀
  let s₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
    (DGFunctor.id (RightModule R E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)) X₁)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)) Y₁)
  have hp : p ≫ s₀ = s ≫ F.map X.source Y.source :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_source R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) X Y
  have hq' : q ≫ t = s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_source R C E a hs hq ha X Y
  have hr : r ≫ s₁ = t ≫ G.map X.source Y.source :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_source R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)) X₁ Y₁
  have hG : (q ≫ r) ≫ s₁ = s ≫ G.map X.source Y.source :=
    (Category.assoc q r s₁).trans
      ((congrArg (fun z => q ≫ z) hr).trans
        (((Category.assoc q t (G.map X.source Y.source)).symm).trans
          (congrArg (fun z => z ≫ G.map X.source Y.source) hq')))
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcomp_square
  · change p ≫ s₀ ≫ _ = (q ≫ r) ≫ s₁ ≫ _
    have hh : F.map X.source Y.source ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj X.source))
          (a Y.source) =
      G.map X.source Y.source ≫ eHomWhiskerRight (Complex R) (a X.source)
        (ForgetEnrichment.of (Complex R) (G.obj Y.source)) := by
      simpa only [EnrichedFunctor.comp_map, EnrichedFunctor.id_map,
        Category.comp_id] using! ha X.source Y.source
    calc
      _ = (p ≫ s₀) ≫ _ := (Category.assoc _ _ _).symm
      _ = (s ≫ F.map X.source Y.source) ≫ _ := congrArg (fun z => z ≫ _) hp
      _ = s ≫ (F.map X.source Y.source ≫ _) := Category.assoc _ _ _
      _ = s ≫ (G.map X.source Y.source ≫ _) := congrArg (fun z => s ≫ z) hh
      _ = (s ≫ G.map X.source Y.source) ≫ _ := (Category.assoc _ _ _).symm
      _ = ((q ≫ r) ≫ s₁) ≫ _ := congrArg (fun z => z ≫ _) hG.symm
      _ = _ := Category.assoc _ _ _
  · have hp' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_replacement R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) X Y
    have hr' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_replacement R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)) X₁ Y₁
    have hq'' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_replacement R C E a hs hq ha X Y
    exact hp'.trans ((Category.assoc q r _).trans
      ((congrArg (fun z => q ≫ z) hr').trans hq'')).symm
  · have hp' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_comparison R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) X Y
    have hr' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_comparison R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)) X₁ Y₁
    have hq'' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_comparison R C E a hs hq ha X Y
    have hqr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison_precompose R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R C (RightModule R E) E G
        (DGFunctor.id (RightModule R E)) X₁)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R C (RightModule R E) E G
        (DGFunctor.id (RightModule R E)) Y₁) q r
    exact hqr.trans ((congrArg (fun z => (Cochain.ofHom q).comp z (zero_add (-1))) hr').trans
      (hq''.trans (congrArg (fun z => z.comp
        (Cochain.ofHom (eHomWhiskerLeft (Complex R)
          (ForgetEnrichment.of (Complex R) X₀.replacement.val) (a Y.source)))
        (add_zero (-1))) hp'.symm)))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
