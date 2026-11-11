module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.EnrichedDifferencePostcompose
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
/-!
概要：全 Hom 自然な次数別全射準同型で、同じ入力と半自由出力を保つ分解対象を作る。
方針：augmentation を後合成し、比較差の全パラメータ上の可換性を照合する。
規約：元の出力の射影性・入力の小ささは不要。使われ方：実分解圏の変更比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
  (hs : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R E (a x))
/-- 同じ実入力と半自由出力を保ち、augmentation だけを指定比較射で後合成する。 -/
def dgModuleResolutionChangeObject (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E G where
  source := X.source
  replacement := X.replacement
  augmentation := X.augmentation ≫ a X.source
  surjective d n := by
    apply (_root_.SerrePositivity.DifferentialGraded.moduleSurjectiveAt_iff_epi R E d n _).2
    have := (_root_.SerrePositivity.DifferentialGraded.moduleSurjectiveAt_iff_epi R E d n _).1 (X.surjective d n)
    have := (_root_.SerrePositivity.DifferentialGraded.moduleSurjectiveAt_iff_epi R E d n _).1 (hs X.source d n)
    simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f]
    infer_instance
  quasiIso := (_root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R E).comp_mem _ _ X.quasiIso (hq X.source)
variable (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x)) (a y) =
  G.map x y ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (a x)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj y)))
include ha in
/-- 元の比較差は、終点の同じ比較射の後合成で新しい比較差へ送られる。 -/
lemma dgModuleResolutionChange_difference
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R C E F X Y ≫
        _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val (F.obj Y.source) (G.obj Y.source)
          (a Y.source) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R C E G
        (dgModuleResolutionChangeObject R C E a hs hq X)
        (dgModuleResolutionChangeObject R C E a hs hq Y) := by
  let K := _root_.SerrePositivity.DifferentialGraded.homObject R C X.source Y.source ⊞ _root_.SerrePositivity.DifferentialGraded.moduleHom R E X.replacement.val Y.replacement.val
  let s : K ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R C X.source Y.source := biprod.fst
  let t : K ⟶ _root_.SerrePositivity.DifferentialGraded.moduleHom R E X.replacement.val Y.replacement.val := biprod.snd
  have hn := congrArg (fun k => s ≫ k) (ha X.source Y.source)
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedDifference_postcompose (Complex R) (ModuleCategory R E) K
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X.replacement.val)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) Y.replacement.val)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj X.source))
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj Y.source))
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj X.source))
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj Y.source))
    (s ≫ F.map X.source Y.source) (s ≫ G.map X.source Y.source) t
    X.augmentation Y.augmentation (a X.source) (a Y.source)
    (by simpa only [Category.assoc] using hn)
  simpa only [s, t, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference, dgModuleResolutionChangeObject,
    _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose, Category.assoc] using! h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
