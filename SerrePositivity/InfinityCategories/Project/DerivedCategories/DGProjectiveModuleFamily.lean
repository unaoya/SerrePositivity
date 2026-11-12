module
public import SerrePositivity.DifferentialGraded.Derived.Basic


/-!
概要：正則非可算 κ の小さい射影的代表族を、実際の加群演算で閉じる。
方針：小さい超限段階と可算個の段階の狭義上界で、同じ代表族の閉性を証明する。
規約：全同型コピーを集めず、全共変 Hom の κ-compact 性は別に証明する。
使われ方：K-7 の実 dg 小模型への対象・小ささ・射影性・直和閉性の供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 同じ実代表族の構成・閉性を保持する。 -/
def DGProjectiveModuleFamily :=
  Σ I : Type u, I → {M : ModuleCategory R D // moduleHomotopicallyProjective R D M}

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveModule_coprod {M N : ModuleCategory R D}
    (hM : moduleHomotopicallyProjective R D M)
    (hN : moduleHomotopicallyProjective R D N) :
    moduleHomotopicallyProjective R D (M ⨿ N) :=
  moduleHomotopicallyProjective_of_iso R D
    (moduleBiprodIso R D M N ≪≫ biprod.isoCoprod M N)
    (moduleHomotopicallyProjective_biprod R D hM hN)

/-- 同じ実代表族の構成・閉性を保持する。 -/
def dgProjectiveFamilyNext (F : DGProjectiveModuleFamily R D) :
    DGProjectiveModuleFamily R D :=
  ⟨PUnit.{u + 1} ⊕ F.1 ⊕ (ℤ × F.1) ⊕ (F.1 × F.1) ⊕
      (Σ i : F.1, Σ j : F.1, (F.2 i).val ⟶ (F.2 j).val) ⊕ (ℕ → F.1), fun k => match k with
    | .inl _ => ⟨moduleZero R D,
        moduleHomotopicallyProjective_of_isZero R D (moduleZero_isZero R D)⟩
    | .inr (.inl i) => F.2 i
    | .inr (.inr (.inl (s, i))) =>
        ⟨(F.2 i).val⟦s⟧, moduleHomotopicallyProjective_shift R D (F.2 i).property s⟩
    | .inr (.inr (.inr (.inl (i, j)))) =>
        ⟨(F.2 i).val ⨿ (F.2 j).val,
          dgProjectiveModule_coprod R D (F.2 i).property (F.2 j).property⟩
    | .inr (.inr (.inr (.inr (.inl ⟨i, j, f⟩)))) =>
        ⟨moduleCone R D f,
          moduleHomotopicallyProjective_cone R D (F.2 i).property (F.2 j).property f⟩
    | .inr (.inr (.inr (.inr (.inr i)))) =>
        ⟨∐ (fun n : ℕ ↦ (F.2 (i n)).val),
          moduleCoproduct_homotopicallyProjective R D _ (fun n ↦ (F.2 (i n)).property)⟩⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveFamilyNext_old (F : DGProjectiveModuleFamily R D) (i : F.1) :
    ∃ j : (dgProjectiveFamilyNext R D F).1,
      (dgProjectiveFamilyNext R D F).2 j = F.2 i := ⟨.inr (.inl i), rfl⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveFamilyNext_zero (F : DGProjectiveModuleFamily R D) :
    ∃ j : (dgProjectiveFamilyNext R D F).1,
      ((dgProjectiveFamilyNext R D F).2 j).val = moduleZero R D := ⟨.inl PUnit.unit, rfl⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveFamilyNext_shift (F : DGProjectiveModuleFamily R D) (s : ℤ) (i : F.1) :
    ∃ j : (dgProjectiveFamilyNext R D F).1,
      ((dgProjectiveFamilyNext R D F).2 j).val = (F.2 i).val⟦s⟧ :=
  ⟨.inr (.inr (.inl (s, i))), rfl⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveFamilyNext_binary (F : DGProjectiveModuleFamily R D) (i j : F.1) :
    ∃ k : (dgProjectiveFamilyNext R D F).1,
      ((dgProjectiveFamilyNext R D F).2 k).val = ((F.2 i).val ⨿ (F.2 j).val) :=
  ⟨.inr (.inr (.inr (.inl (i, j)))), rfl⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveFamilyNext_cone (F : DGProjectiveModuleFamily R D) (i j : F.1)
    (f : (F.2 i).val ⟶ (F.2 j).val) :
    ∃ k : (dgProjectiveFamilyNext R D F).1,
      ((dgProjectiveFamilyNext R D F).2 k).val = moduleCone R D f :=
  ⟨.inr (.inr (.inr (.inr (.inl ⟨i, j, f⟩)))), rfl⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveFamilyNext_countable (F : DGProjectiveModuleFamily R D) (i : ℕ → F.1) :
    ∃ k : (dgProjectiveFamilyNext R D F).1,
      ((dgProjectiveFamilyNext R D F).2 k).val = ∐ (fun n : ℕ ↦ (F.2 (i n)).val) :=
  ⟨.inr (.inr (.inr (.inr (.inr i)))), rfl⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
