module
public import SerrePositivity.InfinityCategories.Derived.HomSquareHEq
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeIdentityWhiskering
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransUnitNaturality
/-!
概要：元の全 Hom 正方形を同じ端点の厳密 dg 自然変換へ反映する。
方針：対象と実射の異種等式によって、抽象的な正方形の一致を移送する。
規約：同じ実作用と指定成分を保つ。使われ方：模型変更の比較同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
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
lemma dgModuleResolutionChangeIdentity_unit_naturality
    (X Y : DGModuleFunctorResolutionObject R C E
      (F.comp (DGFunctor.id (RightModule R E)))) :
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).map X Y ≫ (dgUnitPostcompMap (R := R) (D :=
      (DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))))
      (x := (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).obj X) (y := (dgModuleResolutionPrecompFunctor R C
      (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).obj Y)
      (z := ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)))).obj Y) (dgModuleResolutionChangeIdentityUnitComponent
        R C E F G a hs hq ha Y)) = ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)))).map X Y ≫ (dgUnitPrecompMap (R := R) (D :=
        (DGModuleFunctorResolutionObject R (RightModule R E) E
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
      (DGFunctor.id (RightModule R E)))).obj Y) (dgModuleResolutionChangeIdentityUnitComponent
        R C E F G a hs hq ha X)) := by
  have hB := congrArg₂ (fun x y : (DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))) => homObject R (DGModuleFunctorResolutionObject
      R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))) x y)
    (dgModuleResolutionChangeIdentity_left_obj R C E F X)
    (dgModuleResolutionChangeIdentity_left_obj R C E F Y)
  have hC := congrArg₂ (fun x y : (DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))) => homObject R (DGModuleFunctorResolutionObject
      R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))) x y)
    (dgModuleResolutionChangeIdentity_right_obj R C E F G a hs hq ha X)
    (dgModuleResolutionChangeIdentity_right_obj R C E F G a hs hq ha Y)
  have hD := congrArg₂ (fun x y : (DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))) => homObject R (DGModuleFunctorResolutionObject
      R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))) x y)
    (dgModuleResolutionChangeIdentity_left_obj R C E F X)
    (dgModuleResolutionChangeIdentity_right_obj R C E F G a hs hq ha Y)
  exact hom_square_of_heq hB hC hD
    ((dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).map X Y) (((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)))).map X Y) (dgUnitPostcompMap (R := R) (D :=
        (DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))))
      (x := (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).obj X) (y := (dgModuleResolutionPrecompFunctor R C
      (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).obj Y)
      (z := ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)))).obj Y) (dgModuleResolutionChangeIdentityUnitComponent
        R C E F G a hs hq ha Y)) (dgUnitPrecompMap (R := R) (D :=
          (DGModuleFunctorResolutionObject R (RightModule R E) E
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
      (DGFunctor.id (RightModule R E)))).obj Y) (dgModuleResolutionChangeIdentityUnitComponent
        R C E F G a hs hq ha X))
    (dgModuleResolutionPrecompHom R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) X Y) ((dgModuleResolutionChangeHom R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha X Y) ≫
    dgModuleResolutionPrecompHom R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq X) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq Y))
      (dgModuleIdentityResolutionPostcompAction R E (dgModuleResolutionPrecompObject R C
        (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) X) (dgModuleResolutionPrecompObject R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) Y)
      (G.obj Y.source) (a Y.source) (hs Y.source) (hq Y.source))
        (dgModuleIdentityResolutionPrecompAction R E (dgModuleResolutionPrecompObject R C
          (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) X)
      (dgModuleIdentityResolutionPostcompObject R E (dgModuleResolutionPrecompObject R C
        (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) Y)
        (G.obj Y.source) (a Y.source) (hs Y.source) (hq Y.source))
      (G.obj X.source) (a X.source) (hs X.source) (hq X.source))
    (heq_of_eq (dgModuleResolutionChangeIdentity_left_map R C E F X Y))
    (heq_of_eq (dgModuleResolutionChangeIdentity_right_map R C E F G a hs hq ha X Y))
    (dgModuleResolutionChangeIdentity_post_bridge R C E F G a hs hq ha X Y)
    (dgModuleResolutionChangeIdentity_pre_bridge R C E F G a hs hq ha X Y)
    (dgModuleResolutionPrecompChange_hom_square R C E F G a hs hq ha X Y)
def dgModuleResolutionChangeIdentityStrictNatTrans :
    StrictNatTrans (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))) ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)))) :=
  dgStrictNatTransOfUnitMapNaturality
    (R := R) (F := (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)))) (G := ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)))))
    (dgModuleResolutionChangeIdentityUnitComponent R C E F G a hs hq ha)
    (dgModuleResolutionChangeIdentity_unit_naturality R C E F G a hs hq ha)
end SerrePositivity.InfinityCategories
