module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeIdentityObjects
public import SerrePositivity.InfinityCategories.Derived.DGUnitCompositionMapTransport
/-!
概要：元の端点を保つ単位成分と左右合成を、実分解の同じ計算へ接続する。
方針：対象の一致と成分の異種等式を抽象的な全 Hom 合成へ渡す。
規約：全次数を保持し、出力射影性を仮定しない。使われ方：厳密 dg 自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex DGNerve
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

variable (X Y : DGModuleFunctorResolutionObject R C E
    (F.comp (DGFunctor.id (RightModule R E))))
lemma dgModuleResolutionChangeIdentity_post_bridge :
    HEq (    dgUnitPostcompMap (R := R) (D := (DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))))
      (x := (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).obj X) (y := (dgModuleResolutionPrecompFunctor R C
      (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).obj Y)
      (z := ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)))).obj Y) (dgModuleResolutionChangeIdentityUnitComponent R
      C E F G a hs hq ha Y))
      (dgModuleIdentityResolutionPostcompAction R E (dgModuleResolutionPrecompObject R C
        (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) X) (dgModuleResolutionPrecompObject R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) Y)
        (G.obj Y.source) (a Y.source) (hs Y.source) (hq Y.source)) := by
  exact dgUnitPostcompMap_heq
    (dgModuleResolutionChangeIdentityUnitComponent R C E F G a hs hq ha Y)
      (dgModuleIdentityResolutionPostcompHom R E (dgModuleResolutionPrecompObject R C
        (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) Y)
      (G.obj Y.source) (a Y.source) (hs Y.source) (hq Y.source))
    (dgModuleResolutionChangeIdentity_left_obj R C E F X)
    (dgModuleResolutionChangeIdentity_left_obj R C E F Y)
    (dgModuleResolutionChangeIdentity_right_obj R C E F G a hs hq ha Y)
    (dgModuleResolutionChangeIdentity_component_heq R C E F G a hs hq ha Y)
lemma dgModuleResolutionChangeIdentity_pre_bridge :
    HEq (    dgUnitPrecompMap (R := R) (D := (DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))))
      (x := (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).obj X) (y := ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)))).obj X)
      (z := ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)))).obj Y) (dgModuleResolutionChangeIdentityUnitComponent R
      C E F G a hs hq ha X))
      (dgModuleIdentityResolutionPrecompAction R E (dgModuleResolutionPrecompObject R C
        (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) X)
        (dgModuleIdentityResolutionPostcompObject R E (dgModuleResolutionPrecompObject R C
          (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) Y)
          (G.obj Y.source) (a Y.source) (hs Y.source) (hq Y.source))
        (G.obj X.source) (a X.source) (hs X.source) (hq X.source)) := by
  exact dgUnitPrecompMap_heq
    (dgModuleResolutionChangeIdentityUnitComponent R C E F G a hs hq ha X)
      (dgModuleIdentityResolutionPostcompHom R E (dgModuleResolutionPrecompObject R C
        (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) X)
      (G.obj X.source) (a X.source) (hs X.source) (hq X.source))
    (dgModuleResolutionChangeIdentity_left_obj R C E F X)
    (dgModuleResolutionChangeIdentity_right_obj R C E F G a hs hq ha X)
    (dgModuleResolutionChangeIdentity_right_obj R C E F G a hs hq ha Y)
    (dgModuleResolutionChangeIdentity_component_heq R C E F G a hs hq ha X)
end SerrePositivity.InfinityCategories
