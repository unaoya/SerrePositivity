module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedAdjunction

/-!
# Detection of equivalences of derived Quillen adjunctions

The derived functor is an equivalence precisely when its unit on cofibrant
objects and counit on fibrant objects are invertible. The criterion uses any
chosen localization and any chosen derived functors, not a new homotopy-category
type. Resolution formulas then reduce these checks to specified weak equivalences.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅

open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {HC : Type u₃} [Category.{v₃} HC] {HD : Type u₄} [Category.{v₄} HD]
  (QC : C ⥤ HC) [QC.IsLocalization (weakEquivalences C)]
  (QD : D ⥤ HD) [QD.IsLocalization (weakEquivalences D)]

section Detection

variable {H : Type u₅} [Category.{v₅} H]

/-- Cofibrant objects detect isomorphisms of natural transformations on the
localized category because they represent every object up to isomorphism. -/
lemma isIso_iff_on_cofibrant {F G : HC ⥤ H} (γ : F ⟶ G) :
    IsIso γ ↔ ∀ (X : C), IsCofibrant X → IsIso (γ.app (QC.obj X)) := by
  constructor
  · intro h X _
    infer_instance
  · intro h
    have := (CofibrantObject.localizerMorphism C).essSurj_of_hasLeftResolutions QC
    rw [NatTrans.isIso_iff_isIso_app]
    intro Y
    let T := (CofibrantObject.localizerMorphism C).functor ⋙ QC
    rw [NatTrans.isIso_app_iff_of_iso γ (T.objObjPreimageIso Y).symm]
    exact h (T.objPreimage Y).obj (T.objPreimage Y).property

/-- The dual detection theorem uses fibrant objects. -/
lemma isIso_iff_on_fibrant {F G : HD ⥤ H} (γ : F ⟶ G) :
    IsIso γ ↔ ∀ (Y : D), IsFibrant Y → IsIso (γ.app (QD.obj Y)) := by
  constructor
  · intro h Y _
    infer_instance
  · intro h
    have := (FibrantObject.localizerMorphism D).essSurj_of_hasRightResolutions QD
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    let T := (FibrantObject.localizerMorphism D).functor ⋙ QD
    rw [NatTrans.isIso_app_iff_of_iso γ (T.objObjPreimageIso X).symm]
    exact h (T.objPreimage X).obj (T.objPreimage X).property

end Detection

variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [IsLeftQuillen L] [IsRightQuillen R]
  {LF : HC ⥤ HD} {RF : HD ⥤ HC}
  (α : QC ⋙ LF ⟶ L ⋙ QD) (β : R ⋙ QC ⟶ QD ⋙ RF)
  [LF.IsLeftDerivedFunctor α (weakEquivalences C)]
  [RF.IsRightDerivedFunctor β (weakEquivalences D)]

/-- A Quillen adjunction induces an equivalence exactly when the derived unit
and counit are invertible on cofibrant and fibrant representatives. -/
theorem derived_isEquivalence_iff : LF.IsEquivalence ↔
    (∀ (X : C), IsCofibrant X →
      IsIso ((derivedAdjunction QC QD adj α β).unit.app (QC.obj X))) ∧
    (∀ (Y : D), IsFibrant Y →
      IsIso ((derivedAdjunction QC QD adj α β).counit.app (QD.obj Y))) := by
  constructor
  · intro h
    constructor <;> intro X _ <;> infer_instance
  · rintro ⟨hu, hc⟩
    have := (isIso_iff_on_cofibrant QC (derivedAdjunction QC QD adj α β).unit).2 hu
    have := (isIso_iff_on_fibrant QD (derivedAdjunction QC QD adj α β).counit).2 hc
    exact (derivedAdjunction QC QD adj α β).toEquivalence.isEquivalence_functor

/-- A specified fibrant replacement of LX computes the derived unit. Only
the two indicated weak equivalences are needed; no particular resolution is chosen. -/
lemma derived_unit_isIso_of_weakEquivalence_mate (X : C) [IsCofibrant X]
    (Y : D) [IsFibrant Y] (i : L.obj X ⟶ Y) [WeakEquivalence i]
    [WeakEquivalence (adj.homEquiv X Y i)] :
    IsIso ((derivedAdjunction QC QD adj α β).unit.app (QC.obj X)) := by
  have := leftComparison_isIso QC QD α X
  have := rightComparison_isIso QC QD β Y
  have : IsIso (QD.map i) := Localization.inverts QD (weakEquivalences D) i
    (mem_weakEquivalences i)
  have : IsIso (QC.map (adj.homEquiv X Y i)) := Localization.inverts QC
    (weakEquivalences C) _ (mem_weakEquivalences _)
  have hn := β.naturality i
  dsimp at hn
  have he : (derivedAdjunction QC QD adj α β).unit.app (QC.obj X) ≫
      (RF.map (α.app X) ≫ RF.map (QD.map i)) =
        QC.map (adj.homEquiv X Y i) ≫ β.app Y := by
    rw [← Category.assoc, derivedAdjunction_unit_fac, Category.assoc,
      ← hn, ← Category.assoc, ← QC.map_comp, Adjunction.homEquiv_unit]
  have h : IsIso ((derivedAdjunction QC QD adj α β).unit.app (QC.obj X) ≫
      (RF.map (α.app X) ≫ RF.map (QD.map i))) := by rw [he]; infer_instance
  exact (isIso_comp_right_iff _ _).1 h

/-- A specified cofibrant replacement of RY computes the derived counit. -/
lemma derived_counit_isIso_of_weakEquivalence_mate (X : C) [IsCofibrant X]
    (Y : D) [IsFibrant Y] (p : X ⟶ R.obj Y) [WeakEquivalence p]
    [WeakEquivalence ((adj.homEquiv X Y).symm p)] :
    IsIso ((derivedAdjunction QC QD adj α β).counit.app (QD.obj Y)) := by
  have := leftComparison_isIso QC QD α X
  have := rightComparison_isIso QC QD β Y
  have : IsIso (QC.map p) := Localization.inverts QC (weakEquivalences C) p
    (mem_weakEquivalences p)
  have : IsIso (QD.map ((adj.homEquiv X Y).symm p)) := Localization.inverts QD
    (weakEquivalences D) _ (mem_weakEquivalences _)
  have hn := α.naturality p
  dsimp at hn
  have he : (LF.map (QC.map p) ≫ LF.map (β.app Y)) ≫
      (derivedAdjunction QC QD adj α β).counit.app (QD.obj Y) =
        α.app X ≫ QD.map ((adj.homEquiv X Y).symm p) := by
    rw [Category.assoc, derivedAdjunction_counit_fac, ← Category.assoc,
      hn, Category.assoc, ← QD.map_comp, Adjunction.homEquiv_counit]
  have h : IsIso ((LF.map (QC.map p) ≫ LF.map (β.app Y)) ≫
      (derivedAdjunction QC QD adj α β).counit.app (QD.obj Y)) := by rw [he]; infer_instance
  exact (isIso_comp_left_iff _ _).1 h

include α β

/-- The usual cofibrant-to-fibrant weak-equivalence mate criterion implies
an equivalence of the derived adjunction. The proof constructs the two
replacements from the existing model factorizations. -/
theorem derived_isEquivalence_of_mate_weakEquivalences
    (h : ∀ (X : C), IsCofibrant X → ∀ (Y : D), IsFibrant Y →
      ∀ (f : L.obj X ⟶ Y), WeakEquivalence f ↔ WeakEquivalence (adj.homEquiv X Y f)) :
    LF.IsEquivalence := by
  apply (derived_isEquivalence_iff QC QD adj α β).2
  constructor
  · intro X hX
    have := hX
    let fac := MorphismProperty.factorizationData (trivialCofibrations D) (fibrations D)
      (Limits.terminal.from (L.obj X))
    have : IsFibrant fac.Z :=
      (isFibrant_iff_of_isTerminal fac.p Limits.terminalIsTerminal).2 inferInstance
    have : WeakEquivalence (adj.homEquiv X fac.Z fac.i) :=
      (h X hX fac.Z inferInstance fac.i).1 inferInstance
    exact derived_unit_isIso_of_weakEquivalence_mate QC QD adj α β X fac.Z fac.i
  · intro Y hY
    have := hY
    let fac := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
      (Limits.initial.to (R.obj Y))
    have : IsCofibrant fac.Z :=
      (isCofibrant_iff_of_isInitial fac.i Limits.initialIsInitial).2 inferInstance
    have : WeakEquivalence ((adj.homEquiv fac.Z Y).symm fac.p) := by
      apply (h fac.Z inferInstance Y hY _).2
      simpa using (inferInstanceAs (WeakEquivalence fac.p))
    exact derived_counit_isIso_of_weakEquivalence_mate QC QD adj α β fac.Z Y fac.p

end SerrePositivity.Quillen

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.5.1" (partial := direction) "仮定：抽象モデル圏 C,D の Quillen adjunction、元の weak-equivalence localizations と選んだ左右導来関手（HTT と一致）。結論：全 cofibrant X,fibrant Y の adjoint maps における weak equivalence の iff、すなわち条件 (3) から LF が equivalence、導来随伴により RF も equivalence となる方向は一致。導来同値から全 adjoint maps の判定へ戻す型はこの宣言にはなく、三条件全体の iff とは数えない。"] _root_.SerrePositivity.Quillen.derived_isEquivalence_of_mate_weakEquivalences
