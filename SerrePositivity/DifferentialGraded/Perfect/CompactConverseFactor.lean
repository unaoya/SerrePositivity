module
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseTelescope
public import SerrePositivity.DifferentialGraded.Perfect.UniversalProperty
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # 有限 cell を経由する射と compact 性

compact ⇒ Perf の有限因子分解の基底段階。対象を有限 cell と仮定する条件と、
任意の compact な始域からの射が有限 cell を経由する条件とを区別する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive Pretriangulated
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 射が指定有限 cell の導来像を経由する。 -/
def ModuleFiniteCellFactor (S : Set D) {X Y : DerivedModuleCategory A D} (f : X ⟶ Y) : Prop :=
  ∃ (P : DerivedModuleCategory A D), derivedFiniteCellOver A D S P ∧
    ∃ (a : X ⟶ P) (b : P ⟶ Y), a ≫ b = f

lemma moduleFiniteCellFactor_zero (S : Set D) (X Y : DerivedModuleCategory A D) :
    ModuleFiniteCellFactor A D S (0 : X ⟶ Y) :=
  ⟨0, (derivedFiniteCellOver A D S).prop_zero, 0, 0, zero_comp⟩

lemma ModuleFiniteCellFactor.add {S : Set D} {X Y : DerivedModuleCategory A D}
    {f g : X ⟶ Y} (hf : ModuleFiniteCellFactor A D S f)
    (hg : ModuleFiniteCellFactor A D S g) : ModuleFiniteCellFactor A D S (f + g) := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  obtain ⟨Q, hQ, c, d, hcd⟩ := hg
  have hPQ : derivedFiniteCellOver A D S (P ⊞ Q) :=
    (derivedFiniteCellOver A D S).prop_of_iso (biprod.isoProd P Q).symm
      ((derivedFiniteCellOver A D S).prop_prod P Q hP hQ)
  exact ⟨P ⊞ Q, hPQ, biprod.lift a c, biprod.desc b d,
    by rw [biprod.lift_desc, hab, hcd]⟩

lemma ModuleFiniteCellFactor.postcompose {S : Set D} {X Y Z : DerivedModuleCategory A D}
    {f : X ⟶ Y} (hf : ModuleFiniteCellFactor A D S f) (g : Y ⟶ Z) :
    ModuleFiniteCellFactor A D S (f ≫ g) := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  exact ⟨P, hP, a, b ≫ g, by rw [← Category.assoc, hab]⟩

lemma ModuleFiniteCellFactor.precompose {S : Set D} {X Y Z : DerivedModuleCategory A D}
    {g : Y ⟶ Z} (hg : ModuleFiniteCellFactor A D S g) (f : X ⟶ Y) :
    ModuleFiniteCellFactor A D S (f ≫ g) := by
  obtain ⟨P, hP, a, b, hab⟩ := hg
  exact ⟨P, hP, f ≫ a, b, by rw [Category.assoc, hab]⟩

lemma ModuleFiniteCellFactor.shift {S : Set D} {X Y : DerivedModuleCategory A D}
    {f : X ⟶ Y} (hf : ModuleFiniteCellFactor A D S f) (n : ℤ) :
    ModuleFiniteCellFactor A D S (f⟦n⟧') := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  exact ⟨P⟦n⟧, (derivedFiniteCellOver A D S).le_shift n _ hP,
    a⟦n⟧', b⟦n⟧', by rw [← CategoryTheory.Functor.map_comp, hab]⟩

lemma moduleFiniteCellFactor_sum {S : Set D} {J : Type*}
    {X Y : DerivedModuleCategory A D} (t : Finset J) (f : J → (X ⟶ Y))
    (hf : ∀ j ∈ t, ModuleFiniteCellFactor A D S (f j)) :
    ModuleFiniteCellFactor A D S (∑ j ∈ t, f j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using moduleFiniteCellFactor_zero A D S X Y
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add A D
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- compact な対象から有限 cell の任意の u-small 余積への射は有限 cell を経由する。 -/
lemma moduleCompact_coproduct_finiteCellFactor {S : Set D} {X : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) {J : Type u} (F : J → DerivedModuleCategory A D)
    (hF : ∀ j, derivedFiniteCellOver A D S (F j)) (f : X ⟶ ∐ F) :
    ModuleFiniteCellFactor A D S f := by
  obtain ⟨t, g, hg⟩ := hX J F f
  rw [← hg]
  exact moduleFiniteCellFactor_sum A D t (fun j => g j ≫ Sigma.ι F j)
    (fun j _ => ⟨F j, hF j, g j, Sigma.ι F j, rfl⟩)

/-- 恒等射の有限 cell 因子分解は、既存の Perf の定義そのものである。 -/
lemma modulePerfectOver_iff_id_finiteCellFactor (S : Set D) (X : DerivedModuleCategory A D) :
    modulePerfectOver A D S X ↔ ModuleFiniteCellFactor A D S (𝟙 X) := by
  constructor
  · rintro ⟨P, hP, ⟨r⟩⟩
    exact ⟨P, hP, r.i, r.r, r.retract⟩
  · rintro ⟨P, hP, a, b, hab⟩
    exact ⟨P, hP, ⟨{ i := a, r := b, retract := hab }⟩⟩

/-- 任意の compact な始域からの射に対する有限 cell 因子分解性。 -/
def moduleFiniteCellFactorTarget (S : Set D) : ObjectProperty (DerivedModuleCategory A D) :=
  fun Y => ∀ (X : DerivedModuleCategory A D), moduleCompact A D X →
    ∀ f : X ⟶ Y, ModuleFiniteCellFactor A D S f

lemma moduleFiniteCellFactorTarget_of_finiteCell {S : Set D}
    {Y : DerivedModuleCategory A D} (hY : derivedFiniteCellOver A D S Y) :
    moduleFiniteCellFactorTarget A D S Y :=
  fun _ _ f => ⟨Y, hY, f, 𝟙 Y, Category.comp_id f⟩

lemma moduleFiniteCellFactorTarget_shift {S : Set D} {Y : DerivedModuleCategory A D}
    (hY : moduleFiniteCellFactorTarget A D S Y) (n : ℤ) :
    moduleFiniteCellFactorTarget A D S (Y⟦n⟧) := by
  intro X hX f
  let E := shiftEquiv' (DerivedModuleCategory A D) (-n) n (neg_add_cancel n)
  let e := E.toAdjunction.homEquiv X Y
  have ha := hY _ (moduleCompact_shift A D hX (-n)) (e.symm f)
  have hf := (ha.shift A D n).precompose A D (E.toAdjunction.unit.app X)
  have he : E.toAdjunction.unit.app X ≫ (e.symm f)⟦n⟧' = f :=
    (E.toAdjunction.homEquiv_unit X Y (e.symm f)).symm.trans (e.apply_symm_apply f)
  rwa [he] at hf

lemma moduleFiniteCellFactorTarget_coproduct {S : Set D} {J : Type u}
    (F : J → DerivedModuleCategory A D) (hF : ∀ j, moduleFiniteCellFactorTarget A D S (F j)) :
    moduleFiniteCellFactorTarget A D S (∐ F) := by
  intro X hX f
  obtain ⟨t, g, hg⟩ := hX J F f
  rw [← hg]
  exact moduleFiniteCellFactor_sum A D t (fun j => g j ≫ Sigma.ι F j)
    (fun j _ => (hF j X hX (g j)).postcompose A D (Sigma.ι F j))

end SerrePositivity.DifferentialGraded
