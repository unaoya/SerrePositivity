module

public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverRingMorphisms

/-!
概要：係数と可換な二環図式から、実際の有限型被覆模型の圏への関手を作る。
方針：抽象的な自然変換の可換式で遷移・恒等・合成を確認する。
規約：両辺の環の図式と元の g への可換な自然変換を保持する。
使われ方：B03・B04 の具体的な係数図式の関手の組立て。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable {k R C : Type u} [CommRing k] [CommRing R] [CommRing C]
  [Algebra k R] [Algebra k C] (g : R →ₐ[k] C)
  {J : Type u} [SmallCategory J]
  (F G : J ⥤ CommRingCat.{u}) (τ : F ⟶ G)
  (α : (Functor.const J).obj (CommRingCat.of k) ⟶ F)
  (a : F ⟶ (Functor.const J).obj (CommRingCat.of R))
  (d : G ⟶ (Functor.const J).obj (CommRingCat.of C))
  (hα : ∀ j, α.app j ≫ a.app j = CommRingCat.ofHom (algebraMap k R))
  (hsq : ∀ j, τ.app j ≫ d.app j = a.app j ≫ CommRingCat.ofHom g.toRingHom)
  (hF : ∀ j, (α.app j).hom.FiniteType)
  (hG : ∀ j, ((α ≫ τ).app j).hom.FiniteType)
  (hv : ∀ j, IsAffineVCover (τ.app j).hom)

/-- 抽象的な二環図式の各段は、元の環写像への実際の被覆模型。 -/
def coefficientVCoverDiagramObj (j : J) : CoefficientVCoverModelCategory k g := by
  have hd : (α ≫ τ).app j ≫ d.app j = CommRingCat.ofHom (algebraMap k C) := by
    change (α.app j ≫ τ.app j) ≫ d.app j = _
    rw [Category.assoc, hsq, ← Category.assoc, hα]
    exact CommRingCat.hom_ext g.comp_algebraMap
  exact coefficientVCoverModelObjOfRingHoms g (α.app j).hom ((α ≫ τ).app j).hom
    (hF j) (hG j) (τ.app j).hom (a.app j).hom (d.app j).hom rfl
    (congrArg CommRingCat.Hom.hom (hα j)) (congrArg CommRingCat.Hom.hom hd)
    (congrArg CommRingCat.Hom.hom (hsq j)) (hv j)

/-- 抽象的な二環図式の遷移を、被覆模型の圏の射へ移す。 -/
def coefficientVCoverDiagramMap {j l : J} (w : j ⟶ l) :
    coefficientVCoverDiagramObj g F G τ α a d hα hsq hF hG hv j ⟶
      coefficientVCoverDiagramObj g F G τ α a d hα hsq hF hG hv l := by
  apply coefficientVCoverModelHomMkOfRingHoms g (F.map w).hom (G.map w).hom
  · have H : α.app j ≫ F.map w = α.app l :=
      (α.naturality w).symm.trans (Category.id_comp _)
    exact congrArg CommRingCat.Hom.hom H
  · have H : (α ≫ τ).app j ≫ G.map w = (α ≫ τ).app l :=
      ((α ≫ τ).naturality w).symm.trans (Category.id_comp _)
    exact congrArg CommRingCat.Hom.hom H
  · exact congrArg CommRingCat.Hom.hom (τ.naturality w)
  · have H : F.map w ≫ a.app l = a.app j :=
      (a.naturality w).trans (Category.comp_id _)
    exact congrArg CommRingCat.Hom.hom H
  · have H : G.map w ≫ d.app l = d.app j :=
      (d.naturality w).trans (Category.comp_id _)
    exact congrArg CommRingCat.Hom.hom H

/-- 係数と元の写像に関して自然な二環図式は、実際の被覆模型の関手を与える。 -/
def coefficientVCoverModelFunctorOfRingDiagrams : J ⥤ CoefficientVCoverModelCategory k g where
  obj j := coefficientVCoverDiagramObj g F G τ α a d hα hsq hF hG hv j
  map w := coefficientVCoverDiagramMap g F G τ α a d hα hsq hF hG hv w
  map_id j := by
    apply coefficientVCoverModelHom_ext g
    · exact congrArg CommRingCat.Hom.hom (F.map_id j)
    · exact congrArg CommRingCat.Hom.hom (G.map_id j)
  map_comp f h := by
    apply coefficientVCoverModelHom_ext g
    · exact congrArg CommRingCat.Hom.hom (F.map_comp f h)
    · exact congrArg CommRingCat.Hom.hom (G.map_comp f h)

end SerrePositivity.AlgebraicGeometry
