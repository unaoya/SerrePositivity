module
public import SerrePositivity.InfinityCategories.Derived.DGModuleIdentityResolutionPostcompSquare
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompFunctor
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeFunctor
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
namespace SerrePositivity.InfinityCategories
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
  (X Y : DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id (RightModule R E))))
lemma dgModuleResolutionPrecompChange_hom_square :
    let X₀ := dgModuleResolutionPrecompObject R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) X
    let Y₀ := dgModuleResolutionPrecompObject R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) Y
    let X₁ := dgModuleResolutionChangeObject R C E
      (F := F.comp (DGFunctor.id (RightModule R E)))
      (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq X
    let Y₁ := dgModuleResolutionChangeObject R C E
      (F := F.comp (DGFunctor.id (RightModule R E)))
      (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq Y
    dgModuleResolutionPrecompHom R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) X Y ≫
        dgModuleIdentityResolutionPostcompAction R E X₀ Y₀ (G.obj Y.source)
          (a Y.source) (hs Y.source) (hq Y.source) =
      (dgModuleResolutionChangeHom R C E
      (F := F.comp (DGFunctor.id (RightModule R E)))
      (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha X Y ≫
        dgModuleResolutionPrecompHom R C (RightModule R E) E G
          (DGFunctor.id (RightModule R E)) X₁ Y₁) ≫
        dgModuleIdentityResolutionPrecompAction R E X₀
          (dgModuleIdentityResolutionPostcompObject R E Y₀ (G.obj Y.source)
            (a Y.source) (hs Y.source) (hq Y.source))
          (G.obj X.source) (a X.source) (hs X.source) (hq X.source) := by
  dsimp only
  let X₀ := dgModuleResolutionPrecompObject R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) X
  let Y₀ := dgModuleResolutionPrecompObject R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) Y
  let X₁ := dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq X
  let Y₁ := dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq Y
  let p := dgModuleResolutionPrecompHom R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) X Y
  let q := dgModuleResolutionChangeHom R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha X Y
  let r := dgModuleResolutionPrecompHom R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)) X₁ Y₁
  let s := dgModuleFunctorResolutionSourceHomMap R C E
    (F.comp (DGFunctor.id (RightModule R E))) X Y
  let t := dgModuleFunctorResolutionSourceHomMap R C E
    (G.comp (DGFunctor.id (RightModule R E))) X₁ Y₁
  let s₀ := dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
    (DGFunctor.id (RightModule R E)) X₀ Y₀
  let s₁ := dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
    (DGFunctor.id (RightModule R E))
    (dgModuleResolutionPrecompObject R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)) X₁)
    (dgModuleResolutionPrecompObject R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)) Y₁)
  have hp : p ≫ s₀ = s ≫ F.map X.source Y.source :=
    dgModuleResolutionPrecompHom_source R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) X Y
  have hq' : q ≫ t = s := dgModuleResolutionChangeHom_source R C E a hs hq ha X Y
  have hr : r ≫ s₁ = t ≫ G.map X.source Y.source :=
    dgModuleResolutionPrecompHom_source R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)) X₁ Y₁
  have hG : (q ≫ r) ≫ s₁ = s ≫ G.map X.source Y.source :=
    (Category.assoc q r s₁).trans
      ((congrArg (fun z => q ≫ z) hr).trans
        (((Category.assoc q t (G.map X.source Y.source)).symm).trans
          (congrArg (fun z => z ≫ G.map X.source Y.source) hq')))
  apply dgModuleIdentityResolutionPostcomp_square
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
  · have hp' := dgModuleResolutionPrecompHom_replacement R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) X Y
    have hr' := dgModuleResolutionPrecompHom_replacement R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)) X₁ Y₁
    have hq'' := dgModuleResolutionChangeHom_replacement R C E a hs hq ha X Y
    exact hp'.trans ((Category.assoc q r _).trans
      ((congrArg (fun z => q ≫ z) hr').trans hq'')).symm
  · have hp' := dgModuleResolutionPrecompHom_comparison R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) X Y
    have hr' := dgModuleResolutionPrecompHom_comparison R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)) X₁ Y₁
    have hq'' := dgModuleResolutionChangeHom_comparison R C E a hs hq ha X Y
    have hqr := dgModuleFunctorResolutionHomComparison_precompose R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (dgModuleResolutionPrecompObject R C (RightModule R E) E G
        (DGFunctor.id (RightModule R E)) X₁)
      (dgModuleResolutionPrecompObject R C (RightModule R E) E G
        (DGFunctor.id (RightModule R E)) Y₁) q r
    exact hqr.trans ((congrArg (fun z => (Cochain.ofHom q).comp z (zero_add (-1))) hr').trans
      (hq''.trans (congrArg (fun z => z.comp
        (Cochain.ofHom (eHomWhiskerLeft (Complex R)
          (ForgetEnrichment.of (Complex R) X₀.replacement.val) (a Y.source)))
        (add_zero (-1))) hp'.symm)))
end SerrePositivity.InfinityCategories
