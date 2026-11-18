module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneLoopComponents
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneUnitLoopVertex
public import SerrePositivity.EInfinity.BarrattEccles.Theory.HomologyAlgebraFunctor
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# 指定シフト単位自己同型を実単位へ戻す

DAG XIII §2.2 の零次数の Ω 比較への前段。シフト関手の充満忠実性で
同じ指定自己同型を回収し、零 loop 比較の逆元の符号も実単位自己同型に保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra (pointedGroupMap)
variable (A : Type u) [CommRing A]

/-- 同じ指定シフト単位自己同型の、実単位での一意な逆像。 -/
def unitDeshiftAutomorphism : 𝟙_ (Complex A) ≅ 𝟙_ (Complex A) :=
  (shiftFunctor (Complex A) (1 : ℤ)).preimageIso (unitShiftAutomorphism A)

@[simp]
lemma unitDeshiftAutomorphism_shift_hom :
    ((unitDeshiftAutomorphism A).hom)⟦(1 : ℤ)⟧' = (unitShiftAutomorphism A).hom :=
  (shiftFunctor (Complex A) (1 : ℤ)).map_preimage _

/-- 零 loop の向きの逆元を実際の単位自己同型の負号として保持する。 -/
def signedUnitDeshiftAutomorphism : 𝟙_ (Complex A) ≅ 𝟙_ (Complex A) where
  hom := -(unitDeshiftAutomorphism A).hom
  inv := -(unitDeshiftAutomorphism A).inv
  hom_inv_id := by rw [CategoryTheory.Preadditive.neg_comp_neg, Iso.hom_inv_id]
  inv_hom_id := by rw [CategoryTheory.Preadditive.neg_comp_neg, Iso.inv_hom_id]

/-- 指定基本円の π/H の計算は、元の Γ の比較でも同じ単位類を返す。 -/
lemma gammaUnitCircle_cohomology :
    (((homologyFunctor (ModuleCat A) (.up ℤ) 0).shiftIso
      (1 : ℤ) (-1 : ℤ) (0 : ℤ) (by decide)).app (𝟙_ (Complex A))).hom.hom
        (Multiplicative.toAdd (gammaPiCohomologyEquiv A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧) 0
          (unitCircleClass A))) = _root_.SerrePositivity.HomologyZero.unitClass (𝟙_ (Complex A)) (𝟙 _) := by
  exact congrArg Multiplicative.toAdd (unitCircle_homology A)

/-- 基本円の指定自己同型による像は、実単位の逆像の H⁰ の類になる。 -/
lemma gammaUnitShiftAction_cohomology :
    (((homologyFunctor (ModuleCat A) (.up ℤ) 0).shiftIso
      (1 : ℤ) (-1 : ℤ) (0 : ℤ) (by decide)).app (𝟙_ (Complex A))).hom.hom
        (Multiplicative.toAdd (gammaPiCohomologyEquiv A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧) 0
          (pointedGroupMap 0 ((gammaPointedFunctor A).map (unitShiftAutomorphism A).hom)
            (unitCircleClass A)))) =
      _root_.SerrePositivity.HomologyZero.unitClass (𝟙_ (Complex A)) (unitDeshiftAutomorphism A).hom := by
  let sh := (homologyFunctor (ModuleCat A) (.up ℤ) 0).shiftIso
    (1 : ℤ) (-1 : ℤ) (0 : ℤ) (by decide)
  have hn := sh.hom.naturality (unitDeshiftAutomorphism A).hom
  change homologyMap (((unitDeshiftAutomorphism A).hom)⟦(1 : ℤ)⟧') (-1) ≫
      (sh.app (𝟙_ (Complex A))).hom =
    (sh.app (𝟙_ (Complex A))).hom ≫ homologyMap (unitDeshiftAutomorphism A).hom 0 at hn
  rw [unitDeshiftAutomorphism_shift_hom] at hn
  have hv := congrArg (fun k => k.hom
    (Multiplicative.toAdd (gammaPiCohomologyEquiv A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧) 0
      (unitCircleClass A)))) hn
  rw [gammaPiCohomologyEquiv_naturality]
  change (sh.app (𝟙_ (Complex A))).hom.hom
    ((homologyMap (unitShiftAutomorphism A).hom (-1)).hom _) = _
  refine hv.trans ((congrArg (fun x => (homologyMap (unitDeshiftAutomorphism A).hom 0).hom x)
    (gammaUnitCircle_cohomology A)).trans ?_)
  simpa only [Category.id_comp] using
    (HomologyZero.unitClass_naturality (unitDeshiftAutomorphism A).hom (𝟙 _))

end SerrePositivity.EInfinity.PowerOperation
