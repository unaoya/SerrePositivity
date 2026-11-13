module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraIntH0Naturality
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitMap
public import SerrePositivity.AlgebraicGeometry.RingDirectLimitIntColimit

/-!
概要：代数係数の Čech 図式の実際の Frobenius 系と適合切断の系を作る。
方針：環準同型が Frobenius と可換であることを整数線形の自然性に読む。
規約：各段の遷移は実際の p 冪であり、基底上の線形性は要求しない。
使われ方：F7 の適合切断の順極限と Čech H⁰ の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]
variable (D : Finset ι ⥤ CommAlgCat.{u} R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

include hR in
/-- 基底環で p が零なら、各交叉の代数でも零。 -/
theorem algebraCech_primeCast (T : Finset ι) : (p : D.obj T) = 0 := by
  simpa using congrArg (algebraMap R (D.obj T)) hR

include hR in
/-- 基底環で p が零なら、適合切断代数でも零。 -/
theorem algebraCechEqualizer_primeCast : (p : fullAlgebraCechEqualizer D) = 0 := by
  simpa using congrArg (algebraMap R (fullAlgebraCechEqualizer D)) hR

/-- 交叉ごとの Frobenius 遷移は整数線形な係数図式の射。 -/
def algebraCechIntFrobeniusSystemMap (i j : ℕ) (h : i ≤ j) :
    algebraCechIntDiagram D ⟶ algebraCechIntDiagram D where
  app T := { hom' := {
    toFun := frobeniusDirectSystemMap (D.obj T) p hp
      (algebraCech_primeCast D p hR T) i j h
    map_add' := (frobeniusDirectSystemMap (D.obj T) p hp
      (algebraCech_primeCast D p hR T) i j h).map_add
    map_smul' := by
      intro r x
      convert (frobeniusDirectSystemMap (D.obj T) p hp
        (algebraCech_primeCast D p hR T) i j h).toAddMonoidHom.map_zsmul r x using 1
      · rfl
      · exact congrArg (frobeniusDirectSystemMap (D.obj T) p hp
          (algebraCech_primeCast D p hR T) i j h)
          (int_smul_eq_zsmul (Module.compHom (D.obj T) (Int.castRingHom R)) r x)
      · exact int_smul_eq_zsmul (Module.compHom (D.obj T) (Int.castRingHom R)) r
          (frobeniusDirectSystemMap (D.obj T) p hp
            (algebraCech_primeCast D p hR T) i j h x) } }
  naturality {T U} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (frobeniusDirectSystemMap_naturality p hp
      (algebraCech_primeCast D p hR T) (algebraCech_primeCast D p hR U)
      (D.map f).hom.toRingHom i j h x).symm

/-- 各交叉で同じ実際の Frobenius 順極限を取る係数関手。 -/
def algebraCechFrobeniusCoefficientFunctor : ℕ ⥤ Finset ι ⥤ ModuleCat.{u} ℤ where
  obj _ := algebraCechIntDiagram D
  map f := algebraCechIntFrobeniusSystemMap D p hp hR _ _ (leOfHom f)
  map_id i := by
    apply NatTrans.ext
    funext T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact DirectedSystem.map_self' (frobeniusDirectSystemMap (D.obj T) p hp
      (algebraCech_primeCast D p hR T)) x
  map_comp {i j k} f g := by
    apply NatTrans.ext
    funext T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (DirectedSystem.map_map' (frobeniusDirectSystemMap (D.obj T) p hp
      (algebraCech_primeCast D p hR T)) (leOfHom f) (leOfHom g) x).symm

/-- 適合切断への係数 Frobenius の作用は、切断環自身の同じ Frobenius。 -/
theorem fullAlgebraCechEqualizerAddMap_frobenius (i j : ℕ) (h : i ≤ j)
    (a : fullAlgebraCechEqualizer D) :
    fullAlgebraCechEqualizerAddMap (algebraCechIntFrobeniusSystemMap D p hp hR i j h) a =
      frobeniusDirectSystemMap (fullAlgebraCechEqualizer D) p hp
        (algebraCechEqualizer_primeCast D p hR) i j h a := by
  apply Subtype.ext
  funext t
  change frobeniusDirectSystemMap (D.obj (cechTupleSupport t)) p hp _ i j h (a.val t) =
    (frobeniusDirectSystemMap (fullAlgebraCechEqualizer D) p hp _ i j h a).val t
  rw [frobeniusDirectSystemMap_apply, frobeniusDirectSystemMap_apply]
  rfl

end SerrePositivity.AlgebraicGeometry
