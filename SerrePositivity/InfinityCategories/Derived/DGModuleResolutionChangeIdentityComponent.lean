module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompChangeSquare
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
def dgModuleResolutionChangeIdentityUnitComponent
    (X : DGModuleFunctorResolutionObject R C E
      (F.comp (DGFunctor.id (RightModule R E)))) :
    𝟙_ (Complex R) ⟶ homObject R
      (DGModuleFunctorResolutionObject R (RightModule R E) E
        (DGFunctor.id (A := R) (RightModule R E)))
      ((dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
        (DGFunctor.id (RightModule R E))).obj X)
      (((dgModuleResolutionChangeFunctor R C E
        (F := F.comp (DGFunctor.id (RightModule R E)))
        (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
        (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
          (DGFunctor.id (RightModule R E)))).obj X) :=
  dgModuleIdentityResolutionPostcompHom R E
    (dgModuleResolutionPrecompObject R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) X)
    (G.obj X.source) (a X.source) (hs X.source) (hq X.source)
end SerrePositivity.InfinityCategories
