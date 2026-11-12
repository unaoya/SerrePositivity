module

public import SerrePositivity.AlgebraicGeometry.SchemeOpenCoverCechIntersections
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechFunctor
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechRefinementNaturality

/-!
概要：スキームの逆像による Čech の被覆と、押し出した係数前層の Čech を比較する。
方針：有限交叉と逆像の等式を係数図式の自然同型に移す。
規約：係数環は固定し、異なる二つの空間の Čech 複体を扱う。
使われ方：底変換・閉厚化・Frobenius・模型の遷移に対する共通細分の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
variable (f : X ⟶ Y) (Q : (X.Opens)ᵒᵖ ⥤ ModuleCat.{u} R)
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

/-- 逆像被覆の有限交叉と、押し出した前層の係数図式の自然同型。 -/
def schemeCechPreimageCoefficientIso (U : ι → Y.Opens) :
    openCoverCechDiagram ((Opens.map f.base).op ⋙ Q) U ≅
      openCoverCechDiagram Q (fun i ↦ f ⁻¹ᵁ U i) :=
  NatIso.ofComponents (fun T ↦ Q.mapIso (eqToIso
    (congrArg op (cechOpenIntersection_scheme_preimage f U T)))) (by
      intro T S h
      change Q.map _ ≫ Q.map _ = Q.map _ ≫ Q.map _
      rw [← Q.map_comp, ← Q.map_comp]
      congr 1)

/-- 逆像被覆と押し出した前層の Čech 複体の自然な同型。 -/
def schemeCechPreimageComplexIso (U : ι → Y.Opens) :
    fullCechComplex (openCoverCechDiagram ((Opens.map f.base).op ⋙ Q) U) ≅
      fullCechComplex (openCoverCechDiagram Q (fun i ↦ f ⁻¹ᵁ U i)) :=
  fullCechComplexFunctor.mapIso (schemeCechPreimageCoefficientIso f Q U)

/-- 逆像被覆の比較は、細分の制限と可換。 -/
theorem schemeCechPreimageRefinement_naturality (U : ι → Y.Opens) (V : κ → Y.Opens)
    (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j)) :
    openCoverCechRefinementMap ((Opens.map f.base).op ⋙ Q) U V ρ hρ ≫
        (schemeCechPreimageComplexIso f Q V).hom =
      (schemeCechPreimageComplexIso f Q U).hom ≫
        openCoverCechRefinementMap Q (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ V j) ρ
          (fun j ↦ ((Opens.map f.base).map (homOfLE (hρ j))).le) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  funext t
  change (Q.map _ ≫ Q.map _).hom (a (ρ ∘ t)) = (Q.map _ ≫ Q.map _).hom (a (ρ ∘ t))
  rw [← Q.map_comp, ← Q.map_comp]
  congr 2

variable {P : (Y.Opens)ᵒᵖ ⥤ ModuleCat.{u} R}
variable (η : P ⟶ (Opens.map f.base).op ⋙ Q)

/-- スキームの射に沿う係数の射から、逆像被覆への Čech の射を作る。 -/
def schemeCechPullbackMap (U : ι → Y.Opens) :
    fullCechComplex (openCoverCechDiagram P U) ⟶
      fullCechComplex (openCoverCechDiagram Q (fun i ↦ f ⁻¹ᵁ U i)) :=
  fullCechComplexMap (openCoverCechCoefficientMap η U) ≫ (schemeCechPreimageComplexIso f Q U).hom

/-- 逆像被覆への Čech の射は、細分の制限と可換。 -/
theorem schemeCechPullbackMap_refinement (U : ι → Y.Opens) (V : κ → Y.Opens)
    (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j)) :
    openCoverCechRefinementMap P U V ρ hρ ≫ schemeCechPullbackMap f Q η V =
      schemeCechPullbackMap f Q η U ≫
        openCoverCechRefinementMap Q (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ V j) ρ
          (fun j ↦ ((Opens.map f.base).map (homOfLE (hρ j))).le) := by
  dsimp only [schemeCechPullbackMap]
  rw [← Category.assoc, openCoverCechRefinementMap_naturality U V ρ hρ η,
    Category.assoc, schemeCechPreimageRefinement_naturality]
  simp only [Category.assoc]

/-- 逆像被覆への Čech H の射は、細分の H の射と可換。 -/
theorem schemeCechPullback_homology_refinement (U : ι → Y.Opens) (V : κ → Y.Opens)
    (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j)) (q : ℕ) :
    HomologicalComplex.homologyMap (openCoverCechRefinementMap P U V ρ hρ) q ≫
        HomologicalComplex.homologyMap (schemeCechPullbackMap f Q η V) q =
      HomologicalComplex.homologyMap (schemeCechPullbackMap f Q η U) q ≫
        HomologicalComplex.homologyMap
          (openCoverCechRefinementMap Q (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ V j) ρ
            (fun j ↦ ((Opens.map f.base).map (homOfLE (hρ j))).le)) q := by
  simpa only [HomologicalComplex.homologyMap_comp] using congrArg
    (fun a ↦ HomologicalComplex.homologyMap a q) (schemeCechPullbackMap_refinement f Q η U V ρ hρ)

end SerrePositivity.AlgebraicGeometry
