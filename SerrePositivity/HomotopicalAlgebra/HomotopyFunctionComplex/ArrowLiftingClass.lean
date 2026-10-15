module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-! # Projective lifting classes in an arrow category

A lifting class in the arrow category is analyzed by its left component
and relative pushout map. No model structure on the arrow category is used.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.ArrowLiftingClass
variable {C : Type u} [Category.{v} C] [HasPushouts C]

abbrev objectwise (Q : MorphismProperty C) : MorphismProperty (Arrow C) :=
  Q.inverseImage Arrow.leftFunc ⊓ Q.inverseImage Arrow.rightFunc

abbrev relativeMap {F G : Arrow C} (i : F ⟶ G) :
    pushout F.hom i.left ⟶ G.right :=
  pushout.desc i.right G.hom i.w.symm

@[reassoc (attr := simp)]
lemma inl_relativeMap {F G : Arrow C} (i : F ⟶ G) :
    pushout.inl F.hom i.left ≫ relativeMap i = i.right :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_relativeMap {F G : Arrow C} (i : F ⟶ G) :
    pushout.inr F.hom i.left ≫ relativeMap i = G.hom :=
  pushout.inr_desc _ _ _

lemma mem_of_left_and_relative (Q : MorphismProperty C) {F G : Arrow C} (i : F ⟶ G)
    (hleft : Q.llp i.left) (hrel : Q.llp (relativeMap i)) : (objectwise Q).llp i := by
  intro U V p hp
  have := hleft p.left hp.1
  have := hrel p.right hp.2
  constructor
  intro a b sq
  have sq₀ : CommSq a.left i.left p.left b.left :=
    ⟨congrArg Arrow.Hom.left sq.w⟩
  let l := sq₀.lift
  let t : pushout F.hom i.left ⟶ U.right :=
    pushout.desc a.right (l ≫ U.hom) (by
      rw [← a.w, ← Category.assoc, sq₀.fac_left])
  have sq₁ : CommSq t (relativeMap i) p.right b.right := by
    constructor
    apply pushout.hom_ext
    · simp only [t, pushout.inl_desc_assoc]
      exact congrArg Arrow.Hom.right sq.w
    · simp only [t, pushout.inr_desc_assoc, Category.assoc]
      rw [← p.w, ← Category.assoc, sq₀.fac_right]
      exact b.w
  let k : G ⟶ U := Arrow.homMk l sq₁.lift (by
    have h := congrArg (fun f => pushout.inr F.hom i.left ≫ f) sq₁.fac_left
    simpa only [inr_relativeMap_assoc, t, pushout.inr_desc] using h.symm)
  exact CommSq.HasLift.mk' {
    l := k
    fac_left := by
      apply Arrow.hom_ext
      · exact sq₀.fac_left
      · change i.right ≫ sq₁.lift = a.right
        have h := congrArg (fun f => pushout.inl F.hom i.left ≫ f) sq₁.fac_left
        simpa only [inl_relativeMap_assoc, t, pushout.inl_desc] using h
    fac_right := by
      apply Arrow.hom_ext
      · exact sq₀.fac_right
      · exact sq₁.fac_right }

lemma relative_mem_of_mem (Q : MorphismProperty C) [Q.ContainsIdentities]
    {F G : Arrow C} (i : F ⟶ G) (hi : (objectwise Q).llp i) :
    Q.llp (relativeMap i) := by
  intro X Y p hp
  let q : Arrow.mk (𝟙 X) ⟶ Arrow.mk p := Arrow.homMk (𝟙 X) p
  have hq : objectwise Q q := ⟨Q.id_mem X, hp⟩
  have := hi q hq
  constructor
  intro a b sq
  let a' : F ⟶ Arrow.mk (𝟙 X) :=
    Arrow.homMk (F.hom ≫ pushout.inl F.hom i.left ≫ a)
      (pushout.inl F.hom i.left ≫ a) (by simp)
  let b' : G ⟶ Arrow.mk p := Arrow.homMk (pushout.inr F.hom i.left ≫ a) b (by
    change (pushout.inr F.hom i.left ≫ a) ≫ p = G.hom ≫ b
    rw [Category.assoc, sq.w, inr_relativeMap_assoc])
  have sq' : CommSq a' i q b' := by
    constructor
    apply Arrow.hom_ext
    · change (F.hom ≫ pushout.inl F.hom i.left ≫ a) ≫ 𝟙 X =
        i.left ≫ (pushout.inr F.hom i.left ≫ a)
      rw [Category.comp_id, ← Category.assoc, pushout.condition, Category.assoc]
    · change (pushout.inl F.hom i.left ≫ a) ≫ p = i.right ≫ b
      rw [Category.assoc, sq.w, inl_relativeMap_assoc]
  exact CommSq.HasLift.mk' {
    l := sq'.lift.right
    fac_left := by
      apply pushout.hom_ext
      · rw [inl_relativeMap_assoc]
        exact congrArg Arrow.Hom.right sq'.fac_left
      · rw [inr_relativeMap_assoc, ← sq'.lift.w]
        have h := congrArg Arrow.Hom.left sq'.fac_right
        change sq'.lift.left ≫ 𝟙 X = pushout.inr F.hom i.left ≫ a at h ⊢
        exact h
    fac_right := congrArg Arrow.Hom.right sq'.fac_right }

omit [HasPushouts C] in
lemma left_mem_of_mem [HasTerminal C] (Q : MorphismProperty C) [Q.ContainsIdentities]
    {F G : Arrow C} (i : F ⟶ G) (hi : (objectwise Q).llp i) : Q.llp i.left := by
  intro X Y p hp
  let q : Arrow.mk (terminal.from X) ⟶ Arrow.mk (terminal.from Y) :=
    Arrow.homMk p (𝟙 (⊤_ C)) (by simp)
  have hq : objectwise Q q := ⟨hp, Q.id_mem _⟩
  have := hi q hq
  constructor
  intro a b sq
  let a' : F ⟶ Arrow.mk (terminal.from X) :=
    Arrow.homMk a (terminal.from F.right) (by simp)
  let b' : G ⟶ Arrow.mk (terminal.from Y) :=
    Arrow.homMk b (terminal.from G.right) (by simp)
  have sq' : CommSq a' i q b' := by
    constructor
    apply Arrow.hom_ext
    · exact sq.w
    · exact terminal.hom_ext _ _
  exact CommSq.HasLift.mk' {
    l := sq'.lift.left
    fac_left := congrArg Arrow.Hom.left sq'.fac_left
    fac_right := congrArg Arrow.Hom.left sq'.fac_right }

/-- Projective cofibration recognition, expressed for an arbitrary right class. -/
lemma mem_iff [HasTerminal C] (Q : MorphismProperty C) [Q.ContainsIdentities]
    {F G : Arrow C} (i : F ⟶ G) :
    (objectwise Q).llp i ↔ Q.llp i.left ∧ Q.llp (relativeMap i) :=
  ⟨fun h => ⟨left_mem_of_mem Q i h, relative_mem_of_mem Q i h⟩,
    fun h => mem_of_left_and_relative Q i h.1 h.2⟩

end SerrePositivity.HomotopyFunctionComplex.ArrowLiftingClass
