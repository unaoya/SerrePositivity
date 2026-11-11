module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModuleValuePiChart
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeHomClosedNaturality
/-!
概要：元の実加群評価チャートと全閉射の自然性。
方針：全空間の実辺比較と dg Yoneda 同型の後合成自然性を合成する。
規約：同じ係数射と同じ基礎空間値の射を保持する。
使われ方：coherent bar の transition と余錐の脚のホモロジー比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet HomologicalComplex
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v)

/-- 同じ閉射の coherent 表示による実基礎空間作用。 -/
def dgBarCompactModuleRawValueEdge {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValueSpace R D M ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValueSpace R D N :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallEdgeValue R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1})) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f)

lemma dgBarCompactModuleLiftPostcomposition
    {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f) =
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R PUnit.unit)) f := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorHom_postcompose
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1}))
    (ForgetEnrichment.of (Complex R) (representable R PUnit.unit)) f
  change eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (representable R PUnit.unit)) f ≫ 𝟙 _ =
    𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f) at h
  simpa only [Category.id_comp, Category.comp_id] using h.symm

lemma dgBarCompactModuleValueHomology_naturality
    {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) (q : ℤ) :
    homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f)) q ≫
        (homologyMapIso (dgYonedaIso R PUnit.unit N) q).hom =
      (homologyMapIso (dgYonedaIso R PUnit.unit M) q).hom ≫
        homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) q := by
  rw [dgBarCompactModuleLiftPostcomposition]
  change homologyMap (eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) (representable R PUnit.unit)) f) q ≫
      homologyMap (dgYonedaIso R PUnit.unit (ForgetEnrichment.to (Complex R) N)).hom q =
    homologyMap (dgYonedaIso R PUnit.unit (ForgetEnrichment.to (Complex R) M)).hom q ≫
      homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) q
  simpa only [homologyMap_comp] using
    congrArg (fun φ => homologyMap φ q) (dgYonedaIso_postcompose R PUnit.{1} PUnit.unit f)

lemma dgBarCompactModuleRawValuePiChart_naturality
    {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) (n : ℕ)
    (z : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValueSpace R D M) _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValueSpace R D M) n z) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValuePiChart R D N n).equiv
      ((dgBarCompactModuleRawValueEdge R D f).app _ z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (dgBarCompactModuleRawValueEdge R D f) z a) =
      homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) (-((n + 1 : ℕ) : ℤ))
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValuePiChart R D M n).equiv z a) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiChart_postcompose_naturality
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallPiChart R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M) n)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallPiChart R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj N) n)
    (homologyMapIso (dgYonedaIso R PUnit.unit M) (-((n + 1 : ℕ) : ℤ))).toLinearEquiv.toEquiv
    (homologyMapIso (dgYonedaIso R PUnit.unit N) (-((n + 1 : ℕ) : ℤ))).toLinearEquiv.toEquiv
    (dgBarCompactModuleRawValueEdge R D f) _ _
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallPiChart_closedNaturality R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f) n)
    (fun a => ConcreteCategory.congr_hom
      (dgBarCompactModuleValueHomology_naturality R D f (-((n + 1 : ℕ) : ℤ))) a)

lemma dgBarCompactModuleRawValuePiZeroChart_naturality
    {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) (a) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValuePiZeroChart R D N
      (SSet.mapπ₀ (dgBarCompactModuleRawValueEdge R D f) a) =
      homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) 0
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValuePiZeroChart R D M a) := by
  let C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1})
  let g := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallPiZeroChart_closedNaturality R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) g a
  have h' := congrArg (fun b => (homologyMapIso (dgYonedaIso R PUnit.unit N) 0).hom b) h
  have hn := ConcreteCategory.congr_hom (dgBarCompactModuleValueHomology_naturality R D f 0)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallPiZeroChart R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M) a)
  exact h'.trans hn

/-- 元の native 頂点表示への、同じ実射の輸送。 -/
def dgBarCompactModuleValueEdge {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValueSpace R D (ForgetEnrichment.to (Complex R) M) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValueSpace R D (ForgetEnrichment.to (Complex R) N) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceMapCast (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValueSpace_eq R D (ForgetEnrichment.to (Complex R) M))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValueSpace_eq R D (ForgetEnrichment.to (Complex R) N)) (dgBarCompactModuleRawValueEdge R D f)

lemma dgBarCompactModuleValuePiChart_naturality
    {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChartNaturality
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValuePiChart R D (ForgetEnrichment.to (Complex R) M) n)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValuePiChart R D (ForgetEnrichment.to (Complex R) N) n)
      (dgBarCompactModuleValueEdge R D f)
      (homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) (-((n + 1 : ℕ) : ℤ))).hom := by
  have h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChartNaturality
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValuePiChart R D (ForgetEnrichment.to (Complex R) M) n)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValuePiChart R D (ForgetEnrichment.to (Complex R) N) n)
      (dgBarCompactModuleRawValueEdge R D f)
      (homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) (-((n + 1 : ℕ) : ℤ))).hom :=
    ⟨dgBarCompactModuleRawValuePiChart_naturality R D f n⟩
  exact h.cast (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValueSpace_eq R D (ForgetEnrichment.to (Complex R) M))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValueSpace_eq R D (ForgetEnrichment.to (Complex R) N))

lemma dgBarCompactModuleValuePiZeroChart_naturality
    {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) (a) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValuePiZeroChart R D (ForgetEnrichment.to (Complex R) N)
      (SSet.mapπ₀ (dgBarCompactModuleValueEdge R D f) a) =
      homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) 0
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValuePiZeroChart R D (ForgetEnrichment.to (Complex R) M) a) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiZeroChart_cast_naturality
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValueSpace_eq R D (ForgetEnrichment.to (Complex R) M)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValueSpace_eq R D (ForgetEnrichment.to (Complex R) N))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValuePiZeroChart R D (ForgetEnrichment.to (Complex R) M)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValuePiZeroChart R D (ForgetEnrichment.to (Complex R) N))
    (dgBarCompactModuleRawValueEdge R D f)
    (homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) 0).hom
    (dgBarCompactModuleRawValuePiZeroChart_naturality R D f) a

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
