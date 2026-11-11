module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionChangeIdentityComponent
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (a : ∀ x, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
  (hs : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R E (a x))
  (ha : ∀ x y, (F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))).map x y ≫
    eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x)) (a y) =
    (G.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))).map x y ≫
      eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (a x)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj y)))

variable (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E
    (F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))
lemma dgModuleResolutionChangeIdentity_left_obj :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).obj X = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R C (RightModule
      R E) E F
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) X) := by rfl
lemma dgModuleResolutionChangeIdentity_right_obj :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeFunctor R C E
    (F := F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
    (G := G.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))) a hs hq ha).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)))).obj X = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompObject R E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R C (RightModule R E) E F
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) X)
      (G.obj X.source) (a X.source) (hs X.source) (hq X.source)) := by rfl
lemma dgModuleResolutionChangeIdentity_component_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityUnitComponent R C E F G a hs hq ha X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleIdentityResolutionPostcompHom R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R C
        (_root_.SerrePositivity.DifferentialGraded.RightModule R E) E F
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) X)
      (G.obj X.source) (a X.source) (hs X.source) (hq X.source)) := by rfl
lemma dgModuleResolutionChangeIdentity_left_map :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).map X Y = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R C (RightModule R
      E) E F
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) X Y := rfl
lemma dgModuleResolutionChangeIdentity_right_map :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeFunctor R C E
    (F := F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
    (G := G.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))) a hs hq ha).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)))).map X Y = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E
    (F := F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
    (G := G.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))) a hs hq ha X Y) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E
    (F := F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E
    (F := F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
    (G := G.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))) a hs hq Y)) := rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
