module

public import SerrePositivity.AlgebraicGeometry.SchemeCechCompatibleSections

/-!
概要：一般の開被覆の Čech H⁰ に用いる環を、大域切断の環と比較する。
方針：適合条件の比較と層の貼り合わせを合成し、実際の制限とスカラーを照合する。
規約：導来関手の H⁰ を新しく定義せず、既存の equalizer の環を使う。
使われ方：F7 の有限環の Spec と、元の射影スキームの全射性を結ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (Y : Scheme.{u}) {ι : Type} [DecidableEq ι]
variable (U : ι → Y.Opens) (φ : R →+* Γ(Y, ⊤)) (hcover : (⨆ i, U i) = ⊤)

/-- 実際の Čech の適合切断の環と、大域切断の環の同型。 -/
def schemeCechGlobalSectionsEquiv :
    fullAlgebraCechEqualizer (schemeSectionAlgebraCechDiagram Y φ U) ≃+* Γ(Y, ⊤) :=
  (schemeCechCompatibleSectionsEquiv Y U φ).trans
    (schemeGlobalCompatibleSectionsEquiv Y U hcover).symm

/-- 貼り合わせた大域切断の各開集合への制限は、指定された局所切断。 -/
theorem schemeCechGlobalSectionsEquiv_restrict
    (a : fullAlgebraCechEqualizer (schemeSectionAlgebraCechDiagram Y φ U)) (i : ι) :
    (Y.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op).hom
        (schemeCechGlobalSectionsEquiv Y U φ hcover a) =
      schemeCechSingletonSectionsEquiv Y U φ a.val i :=
  congrArg (fun s ↦ s.val i)
    ((schemeGlobalCompatibleSectionsEquiv Y U hcover).apply_symm_apply
      (schemeCechCompatibleSectionsEquiv Y U φ a))

/-- 大域切断から Čech の切断族への逆写像は、元の構造層の実際の制限。 -/
theorem schemeCechGlobalSectionsEquiv_symm_apply (s : Γ(Y, ⊤)) (t : Fin 1 → ι) :
    ((schemeCechGlobalSectionsEquiv Y U φ hcover).symm s).val t =
      (Y.presheaf.map (homOfLE (show cechOpenIntersection U (cechTupleSupport t) ≤ ⊤
        from le_top)).op).hom s := by
  change (Y.presheaf.map _).hom ((Y.presheaf.map _).hom s) = _
  change (Y.presheaf.map _ ≫ Y.presheaf.map _).hom s = _
  rw [← Y.presheaf.map_comp]
  congr 2

/-- 貼り合わせの同型の逆は、指定した大域スカラーを元の部分代数のスカラーへ送る。 -/
theorem schemeCechGlobalSectionsEquiv_symm_algebraMap (r : R) :
    (schemeCechGlobalSectionsEquiv Y U φ hcover).symm (φ r) =
      algebraMap R (fullAlgebraCechEqualizer (schemeSectionAlgebraCechDiagram Y φ U)) r := by
  apply Subtype.ext
  funext t
  rw [schemeCechGlobalSectionsEquiv_symm_apply]
  rfl

/-- 貼り合わせの環の同型は、指定された基底環上の代数同型でもある。 -/
def schemeCechGlobalSectionsAlgEquiv :
    letI := φ.toAlgebra
    fullAlgebraCechEqualizer (schemeSectionAlgebraCechDiagram Y φ U) ≃ₐ[R] Γ(Y, ⊤) := by
  letI := φ.toAlgebra
  refine { schemeCechGlobalSectionsEquiv Y U φ hcover with commutes' := ?_ }
  intro r
  apply (schemeCechGlobalSectionsEquiv Y U φ hcover).symm.injective
  change (schemeCechGlobalSectionsEquiv Y U φ hcover).symm
    (schemeCechGlobalSectionsEquiv Y U φ hcover _) = _
  rw [RingEquiv.symm_apply_apply]
  exact (schemeCechGlobalSectionsEquiv_symm_algebraMap Y U φ hcover r).symm

end SerrePositivity.AlgebraicGeometry
