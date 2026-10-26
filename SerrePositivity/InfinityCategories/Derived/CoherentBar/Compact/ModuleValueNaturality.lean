module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModuleValuePiChart
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeHomClosedNaturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DoldKanComparison SSet HomologicalComplex
open SerrePositivity.KST.Spectra
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v)

/-- 同じ閉射の coherent 表示による実基礎空間作用。 -/
def dgBarCompactModuleRawValueEdge {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) :
    dgBarCompactModuleRawValueSpace R D M ⟶ dgBarCompactModuleRawValueSpace R D N :=
  dgBarCompactNativeHomSmallEdgeValue R
    (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1})) (dgHomModuleUnit R D)
    ((dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f)

lemma dgBarCompactModuleLiftPostcomposition
    {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) :
    dgClosedPostcomposition R
      (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (x := dgHomModuleUnit R D)
      ((dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f) =
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R PUnit.unit)) f := by
  have h := dgFunctorHom_postcompose
    (dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1}))
    (ForgetEnrichment.of (Complex R) (representable R PUnit.unit)) f
  change eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (representable R PUnit.unit)) f ≫ 𝟙 _ =
    𝟙 _ ≫ dgClosedPostcomposition R
      (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (x := dgHomModuleUnit R D)
      ((dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f) at h
  simpa only [Category.id_comp, Category.comp_id] using h.symm

lemma dgBarCompactModuleValueHomology_naturality
    {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) (q : ℤ) :
    homologyMap (dgClosedPostcomposition R
      (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (x := dgHomModuleUnit R D)
      ((dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f)) q ≫
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
    (z : (dgBarCompactModuleRawValueSpace R D M) _⦋0⦌)
    (a : KanHomotopyGroup (dgBarCompactModuleRawValueSpace R D M) n z) :
    (dgBarCompactModuleRawValuePiChart R D N n).equiv
      ((dgBarCompactModuleRawValueEdge R D f).app _ z)
      (dgBarCompactPiMap n (dgBarCompactModuleRawValueEdge R D f) z a) =
      homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) (-((n + 1 : ℕ) : ℤ))
        ((dgBarCompactModuleRawValuePiChart R D M n).equiv z a) := by
  apply dgBarCompactPiChart_postcompose_naturality
    (dgBarCompactNativeHomSmallPiChart R
      (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (dgHomModuleUnit R D) ((dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M) n)
    (dgBarCompactNativeHomSmallPiChart R
      (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (dgHomModuleUnit R D) ((dgUniverseLiftUp R (RightModule R PUnit.{1})).obj N) n)
    (homologyMapIso (dgYonedaIso R PUnit.unit M) (-((n + 1 : ℕ) : ℤ))).toLinearEquiv.toEquiv
    (homologyMapIso (dgYonedaIso R PUnit.unit N) (-((n + 1 : ℕ) : ℤ))).toLinearEquiv.toEquiv
    (dgBarCompactModuleRawValueEdge R D f) _ _
    (dgBarCompactNativeHomSmallPiChart_closedNaturality R
      (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (dgHomModuleUnit R D) ((dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f) n)
    (fun a => ConcreteCategory.congr_hom
      (dgBarCompactModuleValueHomology_naturality R D f (-((n + 1 : ℕ) : ℤ))) a)

lemma dgBarCompactModuleRawValuePiZeroChart_naturality
    {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) (a) :
    dgBarCompactModuleRawValuePiZeroChart R D N
      (SSet.mapπ₀ (dgBarCompactModuleRawValueEdge R D f) a) =
      homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) 0
        (dgBarCompactModuleRawValuePiZeroChart R D M a) := by
  let C := DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1})
  let g := (dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f
  have h := dgBarCompactNativeHomSmallPiZeroChart_closedNaturality R C (dgHomModuleUnit R D) g a
  have h' := congrArg (fun b => (homologyMapIso (dgYonedaIso R PUnit.unit N) 0).hom b) h
  have hn := ConcreteCategory.congr_hom (dgBarCompactModuleValueHomology_naturality R D f 0)
    (dgBarCompactNativeHomSmallPiZeroChart R C (dgHomModuleUnit R D)
      ((dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M) a)
  exact h'.trans hn

/-- 元の native 頂点表示への、同じ実射の輸送。 -/
def dgBarCompactModuleValueEdge {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) :
    dgBarCompactModuleValueSpace R D (ForgetEnrichment.to (Complex R) M) ⟶ dgBarCompactModuleValueSpace R D (ForgetEnrichment.to (Complex R) N) :=
  dgBarCompactSpaceMapCast (dgBarCompactModuleRawValueSpace_eq R D (ForgetEnrichment.to (Complex R) M))
    (dgBarCompactModuleRawValueSpace_eq R D (ForgetEnrichment.to (Complex R) N)) (dgBarCompactModuleRawValueEdge R D f)

lemma dgBarCompactModuleValuePiChart_naturality
    {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) (n : ℕ) :
    DGBarCompactPiChartNaturality
      (dgBarCompactModuleValuePiChart R D (ForgetEnrichment.to (Complex R) M) n)
      (dgBarCompactModuleValuePiChart R D (ForgetEnrichment.to (Complex R) N) n)
      (dgBarCompactModuleValueEdge R D f)
      (homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) (-((n + 1 : ℕ) : ℤ))).hom := by
  have h : DGBarCompactPiChartNaturality
      (dgBarCompactModuleRawValuePiChart R D (ForgetEnrichment.to (Complex R) M) n)
      (dgBarCompactModuleRawValuePiChart R D (ForgetEnrichment.to (Complex R) N) n)
      (dgBarCompactModuleRawValueEdge R D f)
      (homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) (-((n + 1 : ℕ) : ℤ))).hom :=
    ⟨dgBarCompactModuleRawValuePiChart_naturality R D f n⟩
  exact h.cast (dgBarCompactModuleRawValueSpace_eq R D (ForgetEnrichment.to (Complex R) M))
    (dgBarCompactModuleRawValueSpace_eq R D (ForgetEnrichment.to (Complex R) N))

lemma dgBarCompactModuleValuePiZeroChart_naturality
    {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) (a) :
    dgBarCompactModuleValuePiZeroChart R D (ForgetEnrichment.to (Complex R) N)
      (SSet.mapπ₀ (dgBarCompactModuleValueEdge R D f) a) =
      homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) 0
        (dgBarCompactModuleValuePiZeroChart R D (ForgetEnrichment.to (Complex R) M) a) :=
  dgBarCompactPiZeroChart_cast_naturality
    (dgBarCompactModuleRawValueSpace_eq R D (ForgetEnrichment.to (Complex R) M)) (dgBarCompactModuleRawValueSpace_eq R D (ForgetEnrichment.to (Complex R) N))
    (dgBarCompactModuleRawValuePiZeroChart R D (ForgetEnrichment.to (Complex R) M)) (dgBarCompactModuleRawValuePiZeroChart R D (ForgetEnrichment.to (Complex R) N))
    (dgBarCompactModuleRawValueEdge R D f)
    (homologyMap ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) 0).hom
    (dgBarCompactModuleRawValuePiZeroChart_naturality R D f) a

end SerrePositivity.InfinityCategories
