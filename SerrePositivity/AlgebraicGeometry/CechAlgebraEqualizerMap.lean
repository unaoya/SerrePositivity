module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraH0

/-!
概要：代数係数図式の射が Čech の適合切断環に誘導する実際の代数写像。
方針：各タプルで係数の射を適用し、二つの面との可換性で適合条件を保つ。
規約：環の乗法と基底スカラーは成分ごとの写像で保つ。
使われ方：閉厚化への環の制限と Čech H⁰ の線形写像を照合する入口。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι]
variable {D E F : Finset ι ⥤ CommAlgCat.{u} R}

/-- 係数図式の射が全タプルの切断族に誘導する代数写像。 -/
def fullAlgebraCechCochainsMap (η : D ⟶ E) (k : ℕ) :
    FullRingCechCochains (algebraCechRingDiagram D) k →ₐ[R]
      FullRingCechCochains (algebraCechRingDiagram E) k where
  toFun a t := (η.app (cechTupleSupport t)).hom (a t)
  map_zero' := by funext t; exact map_zero _
  map_one' := by funext t; exact map_one _
  map_add' a b := by funext t; exact map_add _ _ _
  map_mul' a b := by funext t; exact map_mul _ _ _
  commutes' r := by funext t; exact (η.app _).hom.commutes r

/-- タプル上の係数写像は二つの面の制限と可換。 -/
theorem fullAlgebraCechCochainsMap_face (η : D ⟶ E) (i : Fin 2)
    (a : FullRingCechCochains (algebraCechRingDiagram D) 1) :
    fullAlgebraCechFace E i (fullAlgebraCechCochainsMap η 1 a) =
      fullAlgebraCechCochainsMap η 2 (fullAlgebraCechFace D i a) := by
  funext t
  exact congrArg (fun f : D.obj (cechTupleSupport (t ∘ i.succAbove)) ⟶
      E.obj (cechTupleSupport t) ↦ f.hom (a (t ∘ i.succAbove)))
    (η.naturality (homOfLE (cechTupleSupport_face_subset t i))).symm

/-- 係数図式の射が適合切断の部分代数に誘導する写像。 -/
def fullAlgebraCechEqualizerMap (η : D ⟶ E) :
    fullAlgebraCechEqualizer D →ₐ[R] fullAlgebraCechEqualizer E where
  toFun a := ⟨fullAlgebraCechCochainsMap η 1 a.val, by
    change fullAlgebraCechFace E 0 _ = fullAlgebraCechFace E 1 _
    rw [fullAlgebraCechCochainsMap_face, fullAlgebraCechCochainsMap_face]
    exact congrArg (fullAlgebraCechCochainsMap η 2) a.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)
  commutes' r := Subtype.ext ((fullAlgebraCechCochainsMap η 1).commutes r)

/-- 適合切断の写像の各成分は指定された係数の射そのもの。 -/
theorem fullAlgebraCechEqualizerMap_apply (η : D ⟶ E)
    (a : fullAlgebraCechEqualizer D) (t : Fin 1 → ι) :
    (fullAlgebraCechEqualizerMap η a).val t =
      (η.app (cechTupleSupport t)).hom (a.val t) := rfl

/-- 適合切断への恒等係数写像は恒等写像。 -/
theorem fullAlgebraCechEqualizerMap_id (a : fullAlgebraCechEqualizer D) :
    fullAlgebraCechEqualizerMap (𝟙 D) a = a := by
  apply Subtype.ext
  rfl

/-- 適合切断の写像は係数図式の射の合成を保つ。 -/
theorem fullAlgebraCechEqualizerMap_comp (η : D ⟶ E) (θ : E ⟶ F)
    (a : fullAlgebraCechEqualizer D) :
    fullAlgebraCechEqualizerMap (η ≫ θ) a =
      fullAlgebraCechEqualizerMap θ (fullAlgebraCechEqualizerMap η a) := by
  apply Subtype.ext
  rfl

end SerrePositivity.AlgebraicGeometry
