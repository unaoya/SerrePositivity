module
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Shift.Adjunction

/-! # dg enhancementのH⁰比較に使う三角構造の移送

与えたshiftとその比較を維持し、完全忠実同値でdistinguished三角形を引き戻す。
モデル構造・局所化・dg enhancement自体の存在を仮定する補助APIではない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
open scoped ZeroObject
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- 同値の逆関手で零対象を選び、完全忠実性で零性を反映する。 -/
theorem dgComparisonHasZeroObject (e : C ≌ D) [HasZeroObject D] : HasZeroObject C := by
  have hz : IsZero (e.functor.obj (e.inverse.obj (0 : D))) :=
    (isZero_zero D).of_iso (e.counitIso.app (0 : D))
  exact (IsZero.of_full_of_faithful_of_isZero e.functor _ hz).hasZeroObject

variable [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- 既存のshiftを保った同値で三角構造を引き戻す。各公理を対象側の公理から証明する。 -/
@[instance_reducible]
def dgComparisonPretriangulated (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.Additive] :
    Pretriangulated C where
  distinguishedTriangles := {T | e.functor.mapTriangle.obj T ∈ distTriang D}
  isomorphic_distinguished T₁ hT₁ T₂ a :=
    isomorphic_distinguished _ hT₁ _ (e.functor.mapTriangle.mapIso a)
  contractible_distinguished X := by
    let F := e.functor
    have hz : IsZero (F.obj (0 : C)) := F.map_isZero (isZero_zero C)
    apply isomorphic_distinguished _ (contractible_distinguished (F.obj X))
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) hz.isoZero
      (by simp [Functor.mapTriangle, contractibleTriangle, F])
      (by simp [Functor.mapTriangle, contractibleTriangle, F])
      (by simp [Functor.mapTriangle, contractibleTriangle, F])
  distinguished_cocone_triangle {X Y} f := by
    let F := e.functor
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (F.map f)
    let Z' := e.inverse.obj Z
    let z : F.obj Z' ≅ Z := e.counitIso.app Z
    let g' : Y ⟶ Z' := F.preimage (g ≫ z.inv)
    let h' : Z' ⟶ X⟦(1 : ℤ)⟧ :=
      F.preimage (z.hom ≫ h ≫ (F.commShiftIso (1 : ℤ)).inv.app X)
    refine ⟨Z', g', h', isomorphic_distinguished _ hT _ ?_⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) z
      (by simp [Functor.mapTriangle, F])
      (by simp [Functor.mapTriangle, F, g'])
      (by simp [Functor.mapTriangle, F, h', Category.assoc])
  rotate_distinguished_triangle T :=
    (rotate_distinguished_triangle (e.functor.mapTriangle.obj T)).trans
      (distinguished_iff_of_iso ((e.functor.mapTriangleRotateIso).app T))
  complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b hab := by
    let F := e.functor
    have hf : (F.mapTriangle.obj T₁).mor₁ ≫ F.map b =
        F.map a ≫ (F.mapTriangle.obj T₂).mor₁ := by
      change F.map T₁.mor₁ ≫ F.map b = F.map a ≫ F.map T₂.mor₁
      simpa only [F.map_comp] using congrArg F.map hab
    obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
      (F.mapTriangle.obj T₁) (F.mapTriangle.obj T₂) hT₁ hT₂ (F.map a) (F.map b) hf
    refine ⟨F.preimage c, F.map_injective ?_, F.map_injective ?_⟩
    · change F.map T₁.mor₂ ≫ c = F.map b ≫ F.map T₂.mor₂ at hc₂
      simpa only [F.map_comp, F.map_preimage] using hc₂
    · change (F.map T₁.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T₁.obj₁) ≫
        (F.map a)⟦(1 : ℤ)⟧' = c ≫ F.map T₂.mor₃ ≫
          (F.commShiftIso (1 : ℤ)).hom.app T₂.obj₁ at hc₃
      rw [← cancel_mono ((F.commShiftIso (1 : ℤ)).hom.app T₂.obj₁)]
      simpa only [F.map_comp, F.map_preimage, Category.assoc,
        Functor.commShiftIso_hom_naturality] using hc₃

end SerrePositivity.DifferentialGraded
