module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraH0
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCech

/-!
概要：構造層の切断を、指定した基底環上の代数の Čech 図式にする。
方針：大域切断へのスカラー写像を各開集合へ制限する。
規約：対象は実際の切断環、射は実際の制限。
使われ方：射影 Čech H⁰ の有限性を切断の部分代数に移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Opposite _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (Y : Scheme.{u}) (φ : R →+* Γ(Y, ⊤))

/-- 基底環からのスカラーを大域切断経由で開集合に制限した代数構造。 -/
def schemeSectionAlgebra (U : Y.Opens) : Algebra R Γ(Y, U) :=
  ((Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp φ).toAlgebra

/-- 実際の構造層を基底環上の代数の前層として扱う。 -/
def schemeSectionAlgebraPresheaf : Y.Opensᵒᵖ ⥤ CommAlgCat.{u} R where
  obj U := letI := schemeSectionAlgebra Y φ U.unop; CommAlgCat.of R Γ(Y, U.unop)
  map {U V} f := by
    letI := schemeSectionAlgebra Y φ U.unop
    letI := schemeSectionAlgebra Y φ V.unop
    exact CommAlgCat.ofHom
     { __ := (Y.presheaf.map f).hom
       commutes' r := by
         exact (congrArg (fun h ↦ h.hom (φ r))
           (Y.presheaf.map_comp (homOfLE (show U.unop ≤ ⊤ from le_top)).op f)).symm }
  map_id U := by
    letI := schemeSectionAlgebra Y φ U.unop
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact congrArg (fun h ↦ h.hom x) (Y.presheaf.map_id U)
  map_comp {U V W} f g := by
    letI := schemeSectionAlgebra Y φ U.unop
    letI := schemeSectionAlgebra Y φ V.unop
    letI := schemeSectionAlgebra Y φ W.unop
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact congrArg (fun h ↦ h.hom x) (Y.presheaf.map_comp f g)

variable {ι : Type} [DecidableEq ι] (U : ι → Y.Opens)

/-- 開被覆の有限交叉上の、実際の切断代数の図式。 -/
def schemeSectionAlgebraCechDiagram : Finset ι ⥤ CommAlgCat.{u} R where
  obj T := (schemeSectionAlgebraPresheaf Y φ).obj (op (cechOpenIntersection U T))
  map h := (schemeSectionAlgebraPresheaf Y φ).map
    (homOfLE (cechOpenIntersection_antitone U (leOfHom h))).op
  map_id T := by
    convert (schemeSectionAlgebraPresheaf Y φ).map_id (op (cechOpenIntersection U T)) using 1
  map_comp f g := by
    rw [← Functor.map_comp]
    congr 1

/-- 切断代数から忘却した図式と、既存の構造層加群の Čech 図式の比較。 -/
def schemeSectionAlgebraCechModuleIso :
    algebraCechModuleDiagram (schemeSectionAlgebraCechDiagram Y φ U) ≅
      openCoverCechDiagram (schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars φ) U :=
  NatIso.ofComponents (fun T ↦ Iso.refl _) (by
    intro T S f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

/-- 実際の切断の部分代数と、構造層の Čech H⁰ の線形同型。
BST13 Lemma 3.8 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def schemeSectionAlgebraCechH0Equiv :
    fullAlgebraCechEqualizer (schemeSectionAlgebraCechDiagram Y φ U) ≃ₗ[R]
      (fullCechComplex (openCoverCechDiagram
        (schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars φ) U)).homology 0 :=
  (fullAlgebraCechH0Equiv (schemeSectionAlgebraCechDiagram Y φ U)).trans
    (((HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) 0).mapIso
      (fullCechComplexFunctor.mapIso (schemeSectionAlgebraCechModuleIso Y φ U))).toLinearEquiv)

end SerrePositivity.AlgebraicGeometry
