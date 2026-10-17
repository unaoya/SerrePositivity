module
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseFactor

/-! # compact な始域からの有限 cell 因子分解の拡大閉性

Neeman 型の議論：compact な始域と有限 cell の間の射の錐を compact な補助始域とする。
有限 cell の本数を、semifree filtration の高さだけから推測しない。
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

lemma moduleFiniteCellFactorTarget_triangle_obj₂ {S : Set D}
    (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (h₁ : moduleFiniteCellFactorTarget A D S T.obj₁)
    (h₃ : moduleFiniteCellFactorTarget A D S T.obj₃) :
    moduleFiniteCellFactorTarget A D S T.obj₂ := by
  intro X hX f
  obtain ⟨P, hP, a, b, hab⟩ := h₃ X hX (f ≫ T.mor₂)
  obtain ⟨Z, j, k, hZ⟩ := distinguished_cocone_triangle a
  have hPc : moduleCompact A D P := modulePerfectOver_compact A D
    ((derivedFiniteCellOver A D S).le_retractClosure _ hP)
  have hZc : moduleCompact A D Z := moduleCompact_triangle_obj₃ A D _ hZ hX hPc
  have haz : a ≫ (b ≫ T.mor₃) = 0 := by
    rw [← Category.assoc, hab, Category.assoc, comp_distTriang_mor_zero₂₃ _ hT, comp_zero]
  obtain ⟨z, hz⟩ := Triangle.yoneda_exact₂ _ hZ (b ≫ T.mor₃) haz
  change b ≫ T.mor₃ = j ≫ z at hz
  obtain ⟨Q, hQ, l, m, hlm⟩ :=
    moduleFiniteCellFactorTarget_shift A D h₁ 1 Z hZc z
  let δ := j ≫ l
  obtain ⟨E, e, q, hE⟩ := distinguished_cocone_triangle₁ δ
  have hEc : derivedFiniteCellOver A D S E :=
    (derivedFiniteCellOver A D S).ext_of_isTriangulatedClosed₁ _ hE hP hQ
  have hδ : δ ≫ m = b ≫ T.mor₃ := by
    dsimp only [δ]
    rw [Category.assoc, hlm, ← hz]
  obtain ⟨u, hu, _⟩ := complete_distinguished_triangle_morphism₁ _ T.rotate hE
    (rot_of_distTriang _ hT) b m hδ
  change E ⟶ T.obj₂ at u
  change e ≫ b = u ≫ T.mor₂ at hu
  have haδ : a ≫ δ = 0 := by
    have hj : a ≫ j = 0 := comp_distTriang_mor_zero₁₂ _ hZ
    dsimp only [δ]
    rw [← Category.assoc, hj, zero_comp]
  obtain ⟨a', ha'⟩ := Triangle.coyoneda_exact₂ _ hE a haδ
  change X ⟶ E at a'
  change a = a' ≫ e at ha'
  have hdiff : (f - a' ≫ u) ≫ T.mor₂ = 0 := by
    rw [sub_comp, Category.assoc, ← hu, ← Category.assoc, ← ha', hab, sub_self]
  obtain ⟨r, hr⟩ := Triangle.coyoneda_exact₂ T hT (f - a' ≫ u) hdiff
  have hfac : ModuleFiniteCellFactor A D S (a' ≫ u) := ⟨E, hEc, a', u, rfl⟩
  have hrest : ModuleFiniteCellFactor A D S (f - a' ≫ u) := by
    rw [hr]
    exact (h₁ X hX r).postcompose A D T.mor₁
  have h := hfac.add A D hrest
  convert h using 1; abel

instance moduleFiniteCellFactorTargetClosedUnderIso (S : Set D) :
    (moduleFiniteCellFactorTarget A D S).IsClosedUnderIsomorphisms where
  of_iso e hX Y hY f := by
    have h := (hX Y hY (f ≫ e.inv)).postcompose A D e.hom
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

instance moduleFiniteCellFactorTargetStableUnderShift (S : Set D) :
    (moduleFiniteCellFactorTarget A D S).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ h => moduleFiniteCellFactorTarget_shift A D h n⟩

instance moduleFiniteCellFactorTargetContainsZero (S : Set D) :
    (moduleFiniteCellFactorTarget A D S).ContainsZero :=
  ⟨⟨0, isZero_zero _, moduleFiniteCellFactorTarget_of_finiteCell A D
    ((derivedFiniteCellOver A D S).prop_zero)⟩⟩

instance moduleFiniteCellFactorTargetTriangulatedClosed₂ (S : Set D) :
    (moduleFiniteCellFactorTarget A D S).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (moduleFiniteCellFactorTarget_triangle_obj₂ A D)

instance moduleFiniteCellFactorTargetIsTriangulated (S : Set D) :
    (moduleFiniteCellFactorTarget A D S).IsTriangulated where

/-- この因子分解性は、任意の可算 telescope 三角形で閉じている。 -/
lemma moduleFiniteCellFactorTarget_telescope {S : Set D}
    (F : ℕ → DerivedModuleCategory A D) (d : ∀ n, F n ⟶ F (n + 1))
    (hF : ∀ n, moduleFiniteCellFactorTarget A D S (F n)) {Y : DerivedModuleCategory A D}
    (c : (∐ moduleTelescopeFamily A D F) ⟶ Y)
    (b : Y ⟶ (∐ moduleTelescopeFamily A D F)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (moduleTelescopeMap A D F d) c b ∈
      distTriang (DerivedModuleCategory A D)) : moduleFiniteCellFactorTarget A D S Y := by
  intro X hX f
  obtain ⟨n, g, hg⟩ := moduleCompact_telescope_factor A D F d hX c b hT f
  rw [hg]
  exact (hF n X hX g).postcompose A D (Sigma.ι (moduleTelescopeFamily A D F) ⟨n⟩ ≫ c)

lemma modulePerfectOver_of_compact_factorTarget {S : Set D} {X : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) (h : moduleFiniteCellFactorTarget A D S X) :
    modulePerfectOver A D S X :=
  (modulePerfectOver_iff_id_finiteCellFactor A D S X).2 (h X hX (𝟙 X))

end SerrePositivity.DifferentialGraded
