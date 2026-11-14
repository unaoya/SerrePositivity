module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.Semifree
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.ConeBasis
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import Mathlib.CategoryTheory.Limits.Connected
public import SerrePositivity.HomologicalAlgebra.Complex.Basic

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
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
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

private def coproductSpherePresentation {I : Type u}
    {M : I → ModuleCategory S PUnit.{1}}
    (E : ∀ i, ModuleSphereFreePresentation S PUnit.{1} (M i)) :
    ModuleSphereFreePresentation S PUnit.{1} (∐ M) where
  Index := Σ i, (E i).Index
  smallIndex := by
    let : ∀ i, Small.{u} (E i).Index := fun i => (E i).smallIndex
    infer_instance
  object t := (E t.1).object t.2
  degree t := (E t.1).degree t.2
  iso := Sigma.mapIso (fun i => (E i).iso) ≪≫
    sigmaSigmaIso (fun i => (E i).Index)
      (fun i t => freeSphere S PUnit.{1} ((E i).object t) ((E i).degree t))

private abbrev coproductStages {I : Type u} {M : I → ModuleCategory S PUnit.{1}}
    (F : ∀ i, ModuleSemifreeFiltration S PUnit.{1} (M i)) (n : ℕ) :=
  ∐ (fun i => (F i).stage n)

private abbrev coproductTransitions {I : Type u} {M : I → ModuleCategory S PUnit.{1}}
    (F : ∀ i, ModuleSemifreeFiltration S PUnit.{1} (M i)) (n : ℕ) :
    coproductStages S F n ⟶ coproductStages S F (n + 1) :=
  Limits.Sigma.map (fun i => (F i).transition n)

private def coproductFiltrationCocone {I : Type u} {M : I → ModuleCategory S PUnit.{1}}
    (F : ∀ i, ModuleSemifreeFiltration S PUnit.{1} (M i)) :
    Cocone (Functor.ofSequence (coproductTransitions S F)) where
  pt := ∐ (fun i => (F i).cocone.pt)
  ι := NatTrans.ofSequence
    (fun n => Limits.Sigma.map (fun i => (F i).cocone.ι.app n)) (by
      intro n
      rw [Functor.ofSequence_map_homOfLE_succ]
      change Limits.Sigma.map (fun i => (F i).transition n) ≫
        Limits.Sigma.map (fun i => (F i).cocone.ι.app (n + 1)) =
        Limits.Sigma.map (fun i => (F i).cocone.ι.app n) ≫ 𝟙 _
      apply Eq.trans _ (Category.comp_id _).symm
      rw [Sigma.map_comp_map]
      congr 1
      funext i
      simpa only [Functor.ofSequence_map_homOfLE_succ] using
        (F i).cocone.w (homOfLE (Nat.le_succ n)))

private def coproductRestrictionCocone {I : Type u} {M : I → ModuleCategory S PUnit.{1}}
    (F : ∀ i, ModuleSemifreeFiltration S PUnit.{1} (M i))
    (c : Cocone (Functor.ofSequence (coproductTransitions S F))) (i : I) :
    Cocone (Functor.ofSequence (F i).transition) where
  pt := c.pt
  ι := NatTrans.ofSequence
    (fun n => Sigma.ι (fun j => (F j).stage n) i ≫ c.ι.app n) (by
      intro n
      rw [Functor.ofSequence_map_homOfLE_succ]
      change (F i).transition n ≫
        (Sigma.ι (fun j => (F j).stage (n + 1)) i ≫ c.ι.app (n + 1)) =
        (Sigma.ι (fun j => (F j).stage n) i ≫ c.ι.app n) ≫ 𝟙 _
      apply Eq.trans _ (Category.comp_id _).symm
      refine (Sigma.ι_map_assoc (fun j => (F j).transition n) i
        (c.ι.app (n + 1))).symm.trans ?_
      apply congrArg (fun f => Sigma.ι (fun j => (F j).stage n) i ≫ f)
      simpa only [Functor.ofSequence_map_homOfLE_succ] using
        c.w (homOfLE (Nat.le_succ n)))

set_option maxHeartbeats 800000 in
-- 余積の包含と各段の余極限を同時に展開して照合する。
private def coproductFiltrationIsColimit {I : Type u} {M : I → ModuleCategory S PUnit.{1}}
    (F : ∀ i, ModuleSemifreeFiltration S PUnit.{1} (M i)) :
    IsColimit (coproductFiltrationCocone S F) where
  desc c := Sigma.desc (fun i => (F i).isColimit.desc (coproductRestrictionCocone S F c i))
  fac c n := by
    apply Sigma.hom_ext
    intro i
    let d (j : I) := (F j).isColimit.desc (coproductRestrictionCocone S F c j)
    exact (Sigma.ι_map_assoc (fun j => (F j).cocone.ι.app n) i (Sigma.desc d)).trans
      ((congrArg (fun f => (F i).cocone.ι.app n ≫ f) (Sigma.ι_comp_desc d i)).trans
        ((F i).isColimit.fac (coproductRestrictionCocone S F c i) n))
  uniq c m h := by
    apply Sigma.hom_ext
    intro i
    apply (F i).isColimit.hom_ext
    intro n
    let d (j : I) := (F j).isColimit.desc (coproductRestrictionCocone S F c j)
    have hn := congrArg (fun f => Sigma.ι (fun j => (F j).stage n) i ≫ f) (h n)
    have hleft : (F i).cocone.ι.app n ≫
        (Sigma.ι (fun j => (F j).cocone.pt) i ≫ m) =
        Sigma.ι (fun j => (F j).stage n) i ≫ c.ι.app n :=
      (Sigma.ι_map_assoc (fun j => (F j).cocone.ι.app n) i m).symm.trans hn
    have hright : (F i).cocone.ι.app n ≫
        (Sigma.ι (fun j => (F j).cocone.pt) i ≫ Sigma.desc d) =
        Sigma.ι (fun j => (F j).stage n) i ≫ c.ι.app n :=
      (congrArg (fun f => (F i).cocone.ι.app n ≫ f) (Sigma.ι_comp_desc d i)).trans
        ((F i).isColimit.fac (coproductRestrictionCocone S F c i) n)
    exact hleft.trans hright.symm

private def coproductFiltration {I : Type u} {M : I → ModuleCategory S PUnit.{1}}
    (F : ∀ i, ModuleSemifreeFiltration S PUnit.{1} (M i)) :
    ModuleSemifreeFiltration S PUnit.{1} (∐ M) where
  stage := coproductStages S F
  transition := coproductTransitions S F
  initial := coproductSpherePresentation S (fun i => (F i).initial)
  quotient n := ∐ (fun i => (F i).quotient n)
  quotientMap n := Limits.Sigma.map (fun i => (F i).quotientMap n)
  split n := moduleCoproductGradedSplit S PUnit.{1} _ _ (fun i => (F i).split n)
  quotientPresentation n := coproductSpherePresentation S (fun i => (F i).quotientPresentation n)
  cocone := coproductFiltrationCocone S F
  isColimit := coproductFiltrationIsColimit S F
  iso := Sigma.mapIso (fun i => (F i).iso)

/-- 概要：複体の同型は semifree 性を保存する。
方針：一点加群へ同型を戻し、filtration の終端の同型と合成する。
規約：同型の始域に semifree 性を仮定する。使われ方：各種閉性の転送。 -/
theorem complexSemifree_of_iso {P Q : Complex S} (e : P ≅ Q)
    (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S P) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S Q := by
  obtain ⟨F⟩ := hP
  let e' := (moduleEvaluation S PUnit.{1} PUnit.unit).preimageIso
    (X := ForgetEnrichment.of (Complex S) (ringModule S P))
    (Y := ForgetEnrichment.of (Complex S) (ringModule S Q)) e
  exact ⟨{ F with iso := F.iso ≪≫ e' }⟩

/-- 概要：零複体は semifree である。
方針：空の自由 sphere 表示による定数 filtration を評価する。
規約：零複体は通常の圏論的零対象。使われ方：semifree 部分圏の零対象。 -/
theorem complexSemifree_zero : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (0 : Complex S) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree_evaluation S (moduleZero S PUnit.{1})).mpr
    ⟨sphereFreeFiltration S (zeroSpherePresentation S)⟩

/-- 概要：任意の整数次数の sphere 複体は semifree である。
方針：一点だけで添字付けた自由 sphere 表示から定数 filtration を作る。
規約：sphere の微分は零。使われ方：自由セルと完全複体の生成。 -/
theorem complexSemifree_sphere (n : ℤ) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (complexSphere S n) := by
  let E : ModuleSphereFreePresentation S PUnit.{1}
      (freeSphere S PUnit.{1} PUnit.unit n) :=
    { Index := PUnit.{u + 1}
      object := fun _ => PUnit.unit
      degree := fun _ => n
      iso := (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
        freeSphere S PUnit.{1} PUnit.unit n)).symm }
  exact complexSemifree_of_iso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.freeSphereEvaluationIso S n)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree_evaluation S _).mpr ⟨sphereFreeFiltration S E⟩)

/-- 概要：整数シフトは semifree 性を保存する。
方針：filtration の段・商・次数付き分裂をシフトし、余極限の保存を用いる。
規約：sphere の次数はシフト量だけ減る。使われ方：semifree 部分圏のシフト。 -/
theorem complexSemifree_shift {P : Complex S} (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S P) (s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (P⟦s⟧) := by
  obtain ⟨F⟩ := hP
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree_evaluation S _).mpr ⟨shiftedFiltration S F s⟩

/-- 概要：任意の同じ宇宙内の添字による余積は semifree 性を保存する。
方針：各 filtration の段・商を余積にし、余極限の普遍性を成分ごとに示す。
規約：添字に有限性は課さない。使われ方：自由生成と semifree 部分圏の余積。 -/
private theorem complexSemifree_coproduct_sameUniverse {I : Type u} (P : I → Complex S)
    (hP : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (P i)) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (∐ P) := by
  let M (i : I) : ModuleCategory S PUnit.{1} :=
    ForgetEnrichment.of (Complex S) (ringModule S (P i))
  let F (i : I) : ModuleSemifreeFiltration S PUnit.{1} (M i) := (hP i).some
  exact complexSemifree_of_iso S (PreservesCoproduct.iso (ringModuleEquivalence S).functor M)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree_evaluation S _).mpr ⟨coproductFiltration S F⟩)

/-- 概要：任意の u-small な添字型による余積は semifree 性を保存する。
方針：添字型を宇宙 u に縮小し、構成済みの余積 filtration を移送する。
規約：加群宇宙内で小さいことだけを仮定する。使われ方：無限余積と自由生成。 -/
theorem complexSemifree_coproduct {I : Type v} [Small.{u} I] (P : I → Complex S)
    (hP : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (P i)) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (∐ P) := by
  let e : Shrink.{u} I ≃ I := (equivShrink I).symm
  exact complexSemifree_of_iso S (Sigma.reindex e P)
    (complexSemifree_coproduct_sameUniverse S (P ∘ e) (fun i => hP (e i)))

/-- 概要：有限個の semifree 複体の余積は semifree である。
方針：任意余積の閉性を有限添字へ具体化する。
規約：有限個の添字は `Fin n`。使われ方：完全複体の有限直和。 -/
theorem complexSemifree_finiteCoproduct (n : ℕ) (P : Fin n → Complex S)
    (hP : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (P i)) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (∐ P) :=
  complexSemifree_coproduct S P hP

/-- 概要：二項余積は semifree 性を保存する。
方針：二点の添字集合の余積閉性を適用する。
規約：Mathlib の選んだ二項余積。使われ方：二項直和の閉性。 -/
theorem complexSemifree_binaryCoproduct {P Q : Complex S}
    (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S P) (hQ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (P ⨿ Q) :=
  complexSemifree_coproduct S (pairFunction P Q) (fun i => by
    cases i
    · exact hP
    · exact hQ)

/-- 概要：二項直和は semifree 性を保存する。
方針：直和と余積の標準同型で閉性を移す。
規約：Mathlib の二項 biproduct。使われ方：fiber を作る始域。 -/
theorem complexSemifree_binaryBiproduct {P Q : Complex S}
    (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S P) (hQ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (P ⊞ Q) :=
  complexSemifree_of_iso S (biprod.isoCoprod P Q).symm
    (complexSemifree_binaryCoproduct S hP hQ)

/-- 概要：有限直和は semifree 性を保存する。
方針：直和と余積の標準同型で任意余積の閉性を移す。
規約：小さい有限添字集合。使われ方：有限の dg 錐の対象。 -/
theorem complexSemifree_finiteBiproduct {I : Type v} [Finite I] [Small.{u} I]
    (P : I → Complex S) (hP : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (P i)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (⨁ P) :=
  complexSemifree_of_iso S (biproduct.isoCoproduct P).symm
    (complexSemifree_coproduct S P hP)

/-- 概要：semifree 複体間の射の fiber は semifree である。
方針：mapping cone の閉性と整数シフトの閉性を合成する。
規約：fiber は cone の −1 シフト。使われ方：dg fiber の部分圏への制限。 -/
theorem complexSemifree_fiber {P Q : Complex S} (f : P ⟶ Q)
    (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S P) (hQ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S ((CochainComplex.mappingCone f)⟦(-1 : ℤ)⟧) :=
  complexSemifree_shift S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_mappingCone f hP hQ) (-1)

/-- 概要：B ⊕ C から D への任意の射の fiber は semifree である。
方針：二項直和の閉性を fiber の閉性に渡す。
規約：射に追加条件は課さない。使われ方：N7 の dg 極限の Semifree への制限。 -/
theorem complexSemifree_biprodFiber {B C D : Complex S} (f : B ⊞ C ⟶ D)
    (hB : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S B) (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S ((CochainComplex.mappingCone f)⟦(-1 : ℤ)⟧) :=
  complexSemifree_fiber S f (complexSemifree_binaryBiproduct S hB hC) hD

end SerrePositivity.InfinityCategories.Project.DerivedCategories
