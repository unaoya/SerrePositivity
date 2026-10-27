module
public import SerrePositivity.DifferentialGraded.Morita.PerfectKernelImage
public import SerrePositivity.DifferentialGraded.Endomorphism.ProjectiveCriterion

/-!
概要：代表加群の perfect-projective 像から、全 perfect-projective 加群の像を制御する。
方針：有限 cell の像の射影性を帰納で示し、導来 retract をホモトピー retract に戻す。
規約：任意の全次数 dg 関手を用い、左随伴性・全準同型保存・模型の小ささを追加しない。
使われ方：K-S• の実 perfect 値 tensor 評価の制限。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E]

/-- 代表加群の射影的な像から、有限 cell の像の全 Hom 射影性を得る。 -/
lemma perfectDGFunctorImage_projective_finiteCell
    (T : DGFunctor R (RightModule R D) (RightModule R E))
    (hgen : ∀ d : D, moduleHomotopicallyProjective R E
      (ForgetEnrichment.of (Complex R) (T.obj (representable R d))))
    {M : ModuleCategory R D} (hM : moduleFiniteCell R D M) :
    moduleHomotopicallyProjective R E (T.onClosed.obj M) := by
  let F := T.onClosed
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  obtain ⟨c⟩ := hM
  induction c with
  | zero =>
      exact moduleHomotopicallyProjective_of_isZero R E
        (F.map_isZero (moduleZero_isZero R D))
  | generator d _ => exact hgen d
  | @shift M s c ih =>
      exact moduleHomotopicallyProjective_of_iso R E
        (dgModuleFunctorShiftIso R E D T s (ForgetEnrichment.to (Complex R) M)).symm
        (moduleHomotopicallyProjective_shift R E ih s)
  | @sum M N c d ihc ihd =>
      let e := F.mapIso (moduleBiprodIso R D M N) ≪≫ F.mapBiprod M N ≪≫
        (moduleBiprodIso R E (F.obj M) (F.obj N)).symm
      exact moduleHomotopicallyProjective_of_iso R E e.symm
        (moduleHomotopicallyProjective_biprod R E ihc ihd)
  | @cone M N c d f ihc ihd =>
      exact moduleHomotopicallyProjective_of_iso R E (dgModuleFunctorConeIso R D E T f)
        (moduleHomotopicallyProjective_cone R E ihc ihd (F.map f))
  | iso c e ih => exact moduleHomotopicallyProjective_of_iso R E (F.mapIso e) ih

/-- 射影的 perfect 源の導来 retract を実ホモトピー retract へ持ち上げて像を評価する。 -/
lemma perfectDGFunctorImage_projective
    (T : DGFunctor R (RightModule R D) (RightModule R E))
    (hgen : ∀ d : D, moduleHomotopicallyProjective R E
      (ForgetEnrichment.of (Complex R) (T.obj (representable R d))))
    {M : ModuleCategory R D} (hM : moduleHomotopicallyProjective R D M)
    (hPerf : modulePerfect R D ((moduleToDerived R D).obj M)) :
    moduleHomotopicallyProjective R E (T.onClosed.obj M) := by
  let F := T.onClosed
  let Q := moduleToHomotopy R D
  obtain ⟨N, hN, ⟨a⟩⟩ := (modulePerfect_iff R D _).1 hPerf
  have hNP := moduleFiniteCellOver_homotopicallyProjective R D hN
  obtain ⟨i, hi⟩ := moduleProjectiveToDerived_map_surjective R D hM a.i
  obtain ⟨r, hr⟩ := moduleProjectiveToDerived_map_surjective R D hNP a.r
  have h : Q.map (i ≫ r) = Q.map (𝟙 M) := by
    apply (moduleProjectiveDerivedHomEquiv R D hM M).injective
    rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map,
      CategoryTheory.Functor.map_comp, hi, hr, a.retract, CategoryTheory.Functor.map_id]
  apply moduleHomotopicallyProjective_of_homotopyRetract R E (F.map i) (F.map r) _
    (perfectDGFunctorImage_projective_finiteCell R D E T hgen hN)
  have he := congrArg T.onHomotopy.map h
  change (moduleToHomotopy R E).map (F.map (i ≫ r)) =
    (moduleToHomotopy R E).map (F.map (𝟙 M)) at he
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using he

/-- 任意の dg 関手は、代表加群の perfect-projective 像から全 perfect-projective 像を得る。 -/
lemma perfectDGFunctorImage_perfectProjective
    (T : DGFunctor R (RightModule R D) (RightModule R E))
    (hgen : ∀ d : D, modulePerfectProjectiveOver R E Set.univ
      (T.obj (representable R d)))
    {M : RightModule R D} (hM : modulePerfectProjectiveOver R D Set.univ M) :
    modulePerfectProjectiveOver R E Set.univ (T.obj M) :=
  ⟨perfectDGFunctorImage_projective R D E T (fun d => (hgen d).1) hM.1 hM.2,
    perfectDGFunctorImage_projectivePerfect R D E T (fun d => (hgen d).2) hM.1 hM.2⟩

end SerrePositivity.DifferentialGraded.Morita
