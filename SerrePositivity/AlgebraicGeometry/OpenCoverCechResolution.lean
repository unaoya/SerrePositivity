module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCech
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSplitExact

/-!
概要：開被覆の増大 Čech 項を、開集合に自然な前層の複体にする。
方針：開集合との交叉を取った前層に、既存の全タプル Čech 構成を適用する。
規約：零項もタプルの長さ零で表す。被覆の完全性はここでは仮定しない。
使われ方：共通細分の比較を、B1 に渡す二重図式として組み立てる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat R)

/-- 固定した開集合との交叉上の切断を取る前層。 -/
def openCoverIntersectionPresheaf (W : Opens X) : (Opens X)ᵒᵖ ⥤ ModuleCat R where
  obj O := P.obj (op (W ⊓ O.unop))
  map h := P.map (homOfLE (inf_le_inf le_rfl (leOfHom h.unop))).op
  map_id O := by
    convert P.map_id (op (W ⊓ O.unop)) using 1
  map_comp a b := by
    rw [← P.map_comp]
    congr 1

/-- 固定する開集合を狭めるときの交叉前層の制限。 -/
def openCoverIntersectionPresheafMap {W W' : Opens X} (h : W' ≤ W) :
    openCoverIntersectionPresheaf P W ⟶ openCoverIntersectionPresheaf P W' where
  app O := P.map (homOfLE (inf_le_inf h le_rfl)).op
  naturality {O O'} h' := by
    change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
    rw [← P.map_comp, ← P.map_comp]
    congr 1

variable {κ : Type} [LinearOrder κ] (V : κ → Opens X)

/-- 開被覆の増大 Čech の一つの項を前層にする。 -/
def openCoverCechResolution (j : ℕ) : (Opens X)ᵒᵖ ⥤ ModuleCat R where
  obj O := ModuleCat.of R
    (FullCechCochains (openCoverCechDiagram (openCoverIntersectionPresheaf P O.unop) V) j)
  map h := ModuleCat.ofHom (fullCechCochainsMap
    (openCoverCechCoefficientMap (openCoverIntersectionPresheafMap P (leOfHom h.unop)) V) j)
  map_id O := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext t
    change (P.map _).hom (a t) = a t
    have he : (homOfLE (inf_le_inf (show O.unop ≤ O.unop from le_rfl)
        (show cechOpenIntersection V (cechTupleSupport t) ≤ _ from le_rfl))).op =
        𝟙 (op (O.unop ⊓ cechOpenIntersection V (cechTupleSupport t))) := Subsingleton.elim _ _
    rw [he, P.map_id]
    rfl
  map_comp h g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext t
    change (P.map _).hom (a t) = (P.map _ ≫ P.map _).hom (a t)
    rw [← P.map_comp]
    congr 2

/-- 増大 Čech の余境界は開集合について自然。 -/
def openCoverCechResolutionDifferential (j : ℕ) :
    openCoverCechResolution P V j ⟶ openCoverCechResolution P V (j + 1) where
  app O := ModuleCat.ofHom
    (fullCechDifferential (openCoverCechDiagram (openCoverIntersectionPresheaf P O.unop) V) j)
  naturality {O O'} h := by
    apply ModuleCat.hom_ext
    exact (fullCechCochainsMap_comp_differential
      (openCoverCechCoefficientMap (openCoverIntersectionPresheafMap P (leOfHom h.unop)) V) j).symm

/-- 前層としての増大 Čech の微分の二乗は零。 -/
theorem openCoverCechResolutionDifferential_squared (j : ℕ) :
    openCoverCechResolutionDifferential P V j ≫
      openCoverCechResolutionDifferential P V (j + 1) = 0 := by
  ext O a
  exact LinearMap.congr_fun
    (fullCechAugmentedDifferential_squared
      (openCoverCechDiagram (openCoverIntersectionPresheaf P O.unop) V) j) a

end SerrePositivity.AlgebraicGeometry
