module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarProjectiveImage
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleShiftImage
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleConeImage

/-! # 実際の係数拡大は指定生成集合からのperfect対象を保つ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 係数変更したdg圏で、元と同じ指定対象を生成元として取る。 -/
def scalarPerfectGenerators (S : Set D) : Set (ScalarExtension.DGBaseChange φ D) :=
  fun x => (show D from x) ∈ S

lemma scalarModuleExtension_perfect_finiteCellCode {S : Set D} {M : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) :
    modulePerfectOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
      ((moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).obj
        ((ScalarExtension.moduleExtension φ D).obj M)) := by
  let F := ScalarExtension.moduleExtension φ D
  let Q := moduleToDerived A' (ScalarExtension.DGBaseChange φ D)
  let G := F ⋙ Q
  let P := modulePerfectOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
  let : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  induction c with
  | zero => exact P.prop_of_isZero (Q.map_isZero (F.map_isZero (moduleZero_isZero A D)))
  | generator x hx =>
      change P (Q.obj (ForgetEnrichment.of (Complex A')
        (ScalarExtension.rightModule φ D (representable A x))))
      rw [scalarRepresentable_eq]
      exact modulePerfectOver_representable A' (ScalarExtension.DGBaseChange φ D) x hx
  | @shift M s c ih =>
      let e := Q.mapIso (scalarModuleExtensionShiftIso φ D s
        (ForgetEnrichment.to (Complex A) M)) ≪≫ (Q.commShiftIso s).app (F.obj M)
      exact P.prop_of_iso e.symm (P.le_shift s _ ih)
  | @sum M N c d ihc ihd =>
      let e := G.mapIso (moduleBiprodIso A D M N) ≪≫ G.mapBiprod M N ≪≫
        biprod.isoProd (G.obj M) (G.obj N)
      exact P.prop_of_iso e.symm (P.prop_prod _ _ ihc ihd)
  | @cone M N c d f ihc ihd =>
      have hc := P.ext_of_isTriangulatedClosed₃
        (moduleDerivedConeTriangle A' (ScalarExtension.DGBaseChange φ D) (F.map f))
        (moduleDerivedConeTriangle_distinguished A' (ScalarExtension.DGBaseChange φ D) (F.map f))
        ihc ihd
      exact P.prop_of_iso (Q.mapIso (scalarModuleExtensionConeIso φ D f)) hc
  | iso c e ih => exact P.prop_of_iso (G.mapIso e) ih

lemma scalarModuleExtension_perfect_finiteCell {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) :
    modulePerfectOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
      ((moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).obj
        ((ScalarExtension.moduleExtension φ D).obj M)) := by
  obtain ⟨c⟩ := hM
  exact scalarModuleExtension_perfect_finiteCellCode φ D c

lemma scalarModuleExtension_perfect_perfect {S : Set D} {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M)
    (hPerf : modulePerfectOver A D S ((moduleToDerived A D).obj M)) :
    modulePerfectOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
      ((moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).obj
        ((ScalarExtension.moduleExtension φ D).obj M)) := by
  let F := ScalarExtension.moduleExtension φ D
  let Q := moduleToHomotopy A D
  let Q' := moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)
  let H := scalarModuleExtensionHomotopy φ D
  obtain ⟨N, hN, ⟨a⟩⟩ := (modulePerfectOver_iff A D S _).mp hPerf
  have hNP := moduleFiniteCellOver_homotopicallyProjective A D hN
  obtain ⟨i, hi⟩ := moduleProjectiveToDerived_map_surjective A D hM a.i
  obtain ⟨r, hr⟩ := moduleProjectiveToDerived_map_surjective A D hNP a.r
  have h : Q.map (i ≫ r) = Q.map (𝟙 M) := by
    apply (moduleProjectiveDerivedHomEquiv A D hM M).injective
    rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map,
      Functor.map_comp, hi, hr, a.retract, CategoryTheory.Functor.map_id]
  let b : Retract (Q'.obj (F.obj M)) (Q'.obj (F.obj N)) :=
    { i := Q'.map (F.map i)
      r := Q'.map (F.map r)
      retract := by
        have he := congrArg H.map h
        change Q'.map (F.map (i ≫ r)) = Q'.map (F.map (𝟙 M)) at he
        simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using he }
  let L := moduleHomotopyToDerivedClosed A' (ScalarExtension.DGBaseChange φ D)
  let e := moduleToHomotopyDerivedIso A' (ScalarExtension.DGBaseChange φ D)
  let b' := (Retract.ofIso (e.app (F.obj M)).symm).trans
    ((b.map L).trans (Retract.ofIso (e.app (F.obj N))))
  exact modulePerfectOver_of_retract A' (ScalarExtension.DGBaseChange φ D) b'
    (scalarModuleExtension_perfect_finiteCell φ D hN)

end SerrePositivity.DifferentialGraded
