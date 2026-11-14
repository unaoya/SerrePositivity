module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraEqualizerMap
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
概要：整数線形な係数写像が適合切断環の加法群に誘導する写像。
方針：面写像との可換性だけで適合条件を保つ。
規約：基底環上線形でない Frobenius を代数写像と呼ばない。
使われ方：厚化を経由する Frobenius を実際の適合切断へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι]
variable {D E : Finset ι ⥤ CommAlgCat.{u} R}

/-- 代数係数図式の加法群を、整数加群の係数図式として扱う。 -/
abbrev algebraCechIntDiagram (D : Finset ι ⥤ CommAlgCat.{u} R) :=
  algebraCechModuleDiagram D ⋙ ModuleCat.restrictScalars (Int.castRingHom R)

/-- 整数線形な係数写像をタプルごとの加法写像にする。 -/
def fullAlgebraCechCochainsAddMap (η : algebraCechIntDiagram D ⟶ algebraCechIntDiagram E)
    (k : ℕ) : FullRingCechCochains (algebraCechRingDiagram D) k →+
      FullRingCechCochains (algebraCechRingDiagram E) k where
  toFun a t := (η.app (cechTupleSupport t)).hom (a t)
  map_zero' := by funext t; exact map_zero _
  map_add' a b := by funext t; exact map_add _ _ _

/-- 整数線形な係数写像は二つの面の制限と可換。 -/
theorem fullAlgebraCechCochainsAddMap_face
    (η : algebraCechIntDiagram D ⟶ algebraCechIntDiagram E) (i : Fin 2)
    (a : FullRingCechCochains (algebraCechRingDiagram D) 1) :
    fullAlgebraCechFace E i (fullAlgebraCechCochainsAddMap η 1 a) =
      fullAlgebraCechCochainsAddMap η 2 (fullAlgebraCechFace D i a) := by
  funext t
  exact congrArg (fun f : (algebraCechIntDiagram D).obj
      (cechTupleSupport (t ∘ i.succAbove)) ⟶
      (algebraCechIntDiagram E).obj (cechTupleSupport t) ↦ f.hom (a (t ∘ i.succAbove)))
    (η.naturality (homOfLE (cechTupleSupport_face_subset t i))).symm

/-- 整数線形な係数写像が適合切断の加法群に誘導する写像。 -/
def fullAlgebraCechEqualizerAddMap
    (η : algebraCechIntDiagram D ⟶ algebraCechIntDiagram E) :
    fullAlgebraCechEqualizer D →+ fullAlgebraCechEqualizer E where
  toFun a := ⟨fullAlgebraCechCochainsAddMap η 1 a.val, by
    change fullAlgebraCechFace E 0 _ = fullAlgebraCechFace E 1 _
    rw [fullAlgebraCechCochainsAddMap_face, fullAlgebraCechCochainsAddMap_face]
    exact congrArg (fullAlgebraCechCochainsAddMap η 2) a.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)

/-- 適合切断の加法写像の各成分は指定された係数の射。 -/
theorem fullAlgebraCechEqualizerAddMap_apply
    (η : algebraCechIntDiagram D ⟶ algebraCechIntDiagram E)
    (a : fullAlgebraCechEqualizer D) (t : Fin 1 → ι) :
    (fullAlgebraCechEqualizerAddMap η a).val t =
      (η.app (cechTupleSupport t)).hom (a.val t) := rfl

end SerrePositivity.AlgebraicGeometry
