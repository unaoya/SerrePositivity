module
public import SerrePositivity.InfinityCategories.Derived.Semifree
public import SerrePositivity.DifferentialGraded.Module.ShiftCoproduct
public import Mathlib.CategoryTheory.Limits.Connected

/-! # Semifree 複体の閉性

概要：filtration を実際に構成して semifree 性の保存を示す。
方針：一点 dg 加群上で自由表示と分裂を構成し、評価同値で転送する。
規約：加群の宇宙内で小さい添字集合を用いる。
使われ方：semifree 部分圏のシフトと安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded
open scoped ZeroObject
variable (S : Type u) [CommRing S]

private def zeroSpherePresentation :
    ModuleSphereFreePresentation S PUnit.{1} (moduleZero S PUnit.{1}) where
  Index := PEmpty.{u + 1}
  object := PEmpty.elim
  degree := PEmpty.elim
  iso :=
    { hom := 0
      inv := 0
      hom_inv_id := (moduleZero_isZero S PUnit.{1}).eq_of_src _ _
      inv_hom_id := by
        apply Sigma.hom_ext
        intro x
        exact x.elim }

private def identityZeroSplit (M : ModuleCategory S PUnit.{1}) :
    ModuleGradedSplit S PUnit.{1} (𝟙 M) (0 : M ⟶ moduleZero S PUnit.{1}) where
  retraction _ _ := 𝟙 _
  section_ _ _ := 0
  inclusion_retraction _ _ := by simp
  section_projection _ n := by
    have hz := (HomologicalComplex.eval (ModuleCat S) (.up ℤ) n).map_isZero
      ((moduleEvaluation S PUnit.{1} PUnit.unit).map_isZero (moduleZero_isZero S PUnit.{1}))
    exact hz.eq_of_src _ _
  section_retraction _ _ := by simp
  inclusion_projection := by simp
  decomposition _ _ := by simp
  retraction_naturality _ _ _ _ _ _ _ := Category.comp_id _
  section_naturality _ _ _ _ _ _ _ := by simp

private def identitySequenceIso (M : ModuleCategory S PUnit.{1}) :
    Functor.ofSequence (fun _ : ℕ => 𝟙 M) ≅ (Functor.const ℕ).obj M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f =>
    (NatTrans.ofSequence
      (F := Functor.ofSequence (fun _ : ℕ => 𝟙 M)) (G := (Functor.const ℕ).obj M)
      (fun _ => 𝟙 M) (by intro n; simp only [Functor.ofSequence_map_homOfLE_succ,
        Functor.const_obj_map])).naturality f)

private def natConstColimit (M : ModuleCategory S PUnit.{1}) :
    IsColimit (constCocone ℕ M) where
  desc c := c.ι.app 0
  fac c n := by simpa using (c.w (homOfLE (Nat.zero_le n))).symm
  uniq c m h := by simpa using h 0

private def sphereFreeFiltration {M : ModuleCategory S PUnit.{1}}
    (E : ModuleSphereFreePresentation S PUnit.{1} M) :
    ModuleSemifreeFiltration S PUnit.{1} M where
  stage _ := M
  transition _ := 𝟙 M
  initial := E
  quotient _ := moduleZero S PUnit.{1}
  quotientMap _ := 0
  split _ := identityZeroSplit S M
  quotientPresentation _ := zeroSpherePresentation S
  cocone := (Cocone.precompose (identitySequenceIso S M).hom).obj (constCocone ℕ M)
  isColimit := (IsColimit.precomposeHomEquiv (identitySequenceIso S M) _).2
    (natConstColimit S M)
  iso := Iso.refl M

private def shiftedSpherePresentation {M : ModuleCategory S PUnit.{1}}
    (E : ModuleSphereFreePresentation S PUnit.{1} M) (s : ℤ) :
    ModuleSphereFreePresentation S PUnit.{1} (M⟦s⟧) where
  Index := E.Index
  smallIndex := E.smallIndex
  object := E.object
  degree t := E.degree t - s
  iso := (shiftFunctor _ s).mapIso E.iso ≪≫
    freeSphereCoproductShiftIso S PUnit.{1} E.object E.degree s

private def shiftedGradedSplit {M N P : ModuleCategory S PUnit.{1}}
    {f : M ⟶ N} {g : N ⟶ P} (F : ModuleGradedSplit S PUnit.{1} f g) (s : ℤ) :
    ModuleGradedSplit S PUnit.{1} (f⟦s⟧') (g⟦s⟧') where
  retraction x n := F.retraction x (n + s)
  section_ x n := F.section_ x (n + s)
  inclusion_retraction x n := by
    change ((moduleEvaluation S PUnit.{1} x).map (moduleShiftMap S PUnit.{1} s f)).f n ≫
      F.retraction x (n + s) = _
    rw [moduleShiftMap_eval]
    exact F.inclusion_retraction x (n + s)
  section_projection x n := by
    change F.section_ x (n + s) ≫
      ((moduleEvaluation S PUnit.{1} x).map (moduleShiftMap S PUnit.{1} s g)).f n = _
    rw [moduleShiftMap_eval]
    exact F.section_projection x (n + s)
  section_retraction x n := F.section_retraction x (n + s)
  inclusion_projection := by
    rw [← Functor.map_comp, F.inclusion_projection, Functor.map_zero]
  decomposition x n := by
    dsimp only [moduleShiftFunctor_eq, moduleShiftFunctor, moduleShiftObj]
    rw [moduleShiftMap_eval, moduleShiftMap_eval]
    change F.retraction x (n + s) ≫ ((moduleEvaluation S PUnit.{1} x).map f).f (n + s) +
      ((moduleEvaluation S PUnit.{1} x).map g).f (n + s) ≫ F.section_ x (n + s) = 𝟙 _
    exact F.decomposition x (n + s)
  retraction_naturality x y p i j hij a := by
    change (((shiftModule s (ForgetEnrichment.to (Complex S) N)).map _ _).f p a).v
        i j hij ≫ F.retraction y (j + s) =
      F.retraction x (i + s) ≫
        (((shiftModule s (ForgetEnrichment.to (Complex S) M)).map _ _).f p a).v i j hij
    rw [shiftModule_map_v, shiftModule_map_v, Linear.units_smul_comp,
      Linear.comp_units_smul]
    exact congrArg ((s * p).negOnePow • ·)
      (F.retraction_naturality x y p (i + s) (j + s) (by omega) a)
  section_naturality x y p i j hij a := by
    change F.section_ x (i + s) ≫
        (((shiftModule s (ForgetEnrichment.to (Complex S) N)).map _ _).f p a).v i j hij =
      (((shiftModule s (ForgetEnrichment.to (Complex S) P)).map _ _).f p a).v i j hij ≫
        F.section_ y (j + s)
    rw [shiftModule_map_v, shiftModule_map_v, Linear.units_smul_comp,
      Linear.comp_units_smul]
    exact congrArg ((s * p).negOnePow • ·)
      (F.section_naturality x y p (i + s) (j + s) (by omega) a)

private def sequenceShiftIso (F : ℕ ⥤ ModuleCategory S PUnit.{1}) (s : ℤ) :
    Functor.ofSequence (fun n => (F.map (homOfLE (Nat.le_succ n)))⟦s⟧') ≅
      F ⋙ shiftFunctor _ s :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f =>
    (NatTrans.ofSequence (F := Functor.ofSequence
      (fun n => (F.map (homOfLE (Nat.le_succ n)))⟦s⟧'))
      (G := F ⋙ shiftFunctor _ s) (fun _ => 𝟙 _)
      (by intro n; simp only [Functor.ofSequence_map_homOfLE_succ,
        Functor.comp_map, Category.comp_id, Category.id_comp])).naturality f)

private def filtrationShiftDiagramIso {M : ModuleCategory S PUnit.{1}}
    (F : ModuleSemifreeFiltration S PUnit.{1} M) (s : ℤ) :
    Functor.ofSequence (fun n => (F.transition n)⟦s⟧') ≅
      Functor.ofSequence F.transition ⋙ shiftFunctor _ s := by
  simpa only [Functor.ofSequence_map_homOfLE_succ] using
    sequenceShiftIso S (Functor.ofSequence F.transition) s

set_option maxHeartbeats 800000 in
-- 余極限の移送と列の比較を同時に照合するため、既定の展開量を超える。
private def shiftedFiltration {M : ModuleCategory S PUnit.{1}}
    (F : ModuleSemifreeFiltration S PUnit.{1} M) (s : ℤ) :
    ModuleSemifreeFiltration S PUnit.{1} (M⟦s⟧) where
  stage n := (F.stage n)⟦s⟧
  transition n := (F.transition n)⟦s⟧'
  initial := shiftedSpherePresentation S F.initial s
  quotient n := (F.quotient n)⟦s⟧
  quotientMap n := (F.quotientMap n)⟦s⟧'
  split n := shiftedGradedSplit S (F.split n) s
  quotientPresentation n := shiftedSpherePresentation S (F.quotientPresentation n) s
  cocone := (Cocone.precompose (filtrationShiftDiagramIso S F s).hom).obj
    ((shiftFunctor _ s).mapCocone F.cocone)
  isColimit := (IsColimit.precomposeHomEquiv
    (filtrationShiftDiagramIso S F s) _).2
    (isColimitOfPreserves (shiftFunctor _ s) F.isColimit)
  iso := (shiftFunctor _ s).mapIso F.iso

/-- 概要：複体の同型は semifree 性を保存する。
方針：一点加群へ同型を戻し、filtration の終端の同型と合成する。
規約：同型の始域に semifree 性を仮定する。使われ方：各種閉性の転送。 -/
theorem complexSemifree_of_iso {P Q : Complex S} (e : P ≅ Q)
    (hP : complexSemifree S P) : complexSemifree S Q := by
  obtain ⟨F⟩ := hP
  let e' := (moduleEvaluation S PUnit.{1} PUnit.unit).preimageIso
    (X := ForgetEnrichment.of (Complex S) (ringModule S P))
    (Y := ForgetEnrichment.of (Complex S) (ringModule S Q)) e
  exact ⟨{ F with iso := F.iso ≪≫ e' }⟩

/-- 概要：零複体は semifree である。
方針：空の自由 sphere 表示による定数 filtration を評価する。
規約：零複体は通常の圏論的零対象。使われ方：semifree 部分圏の零対象。 -/
theorem complexSemifree_zero : complexSemifree S (0 : Complex S) := by
  exact (complexSemifree_evaluation S (moduleZero S PUnit.{1})).mpr
    ⟨sphereFreeFiltration S (zeroSpherePresentation S)⟩

/-- 概要：任意の整数次数の sphere 複体は semifree である。
方針：一点だけで添字付けた自由 sphere 表示から定数 filtration を作る。
規約：sphere の微分は零。使われ方：自由セルと完全複体の生成。 -/
theorem complexSemifree_sphere (n : ℤ) : complexSemifree S (complexSphere S n) := by
  let E : ModuleSphereFreePresentation S PUnit.{1}
      (freeSphere S PUnit.{1} PUnit.unit n) :=
    { Index := PUnit.{u + 1}
      object := fun _ => PUnit.unit
      degree := fun _ => n
      iso := (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
        freeSphere S PUnit.{1} PUnit.unit n)).symm }
  exact complexSemifree_of_iso S (freeSphereEvaluationIso S n)
    ((complexSemifree_evaluation S _).mpr ⟨sphereFreeFiltration S E⟩)

/-- 概要：整数シフトは semifree 性を保存する。
方針：filtration の段・商・次数付き分裂をシフトし、余極限の保存を用いる。
規約：sphere の次数はシフト量だけ減る。使われ方：semifree 部分圏のシフト。 -/
theorem complexSemifree_shift {P : Complex S} (hP : complexSemifree S P) (s : ℤ) :
    complexSemifree S (P⟦s⟧) := by
  obtain ⟨F⟩ := hP
  exact (complexSemifree_evaluation S _).mpr ⟨shiftedFiltration S F s⟩

end SerrePositivity.InfinityCategories
