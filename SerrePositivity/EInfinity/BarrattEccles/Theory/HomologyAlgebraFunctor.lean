module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyAlgebra

/-!
# Barratt–Eccles 代数の H⁰ 関手

## 概要
Berger–Fresse §1 の積と単位を備えた H⁰ を可換代数の関手にする。

## 方針
厳密代数の射が演算を保つことを、閉零次の代表に適用する。

## 規約
底の加群の射は既存のホモロジー関手の射を使う。

## 使われ方
M13 の係数比較と導来代数の `pi0` 欄。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.HomologyZero

open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded

variable {A : Type u} [CommRing A] {K L : Complex A}

private def actualCycles (K : Complex A) :
    ModuleCat.of A (zeroCycles K) ≅ K.cycles 0 :=
  (K.sc' (-1) 0 1).moduleCatCyclesIso.symm ≪≫
    (K.cyclesIsoSc' (-1) 0 1 (by simp [CochainComplex.prev])
      (by simp [CochainComplex.next])).symm

private lemma actualCycles_i (K : Complex A) :
    (actualCycles K).hom ≫ K.iCycles 0 =
      (K.sc' (-1) 0 1).moduleCatLeftHomologyData.i := by
  simp [actualCycles]

private lemma actualCycles_π (K : Complex A) :
    (actualCycles K).hom ≫ K.homologyπ 0 = ModuleCat.ofHom (_root_.SerrePositivity.HomologyZero.classMap K) := by
  simp only [actualCycles, Iso.trans_hom, Iso.symm_hom, Category.assoc, _root_.SerrePositivity.HomologyZero.classMap,
    _root_.SerrePositivity.HomologyZero.quotientIso, Iso.trans_inv, ModuleCat.ofHom_hom]
  rw [← HomologicalComplex.π_homologyIsoSc'_inv,
    ShortComplex.moduleCatCyclesIso_inv_π_assoc]

/-- 単位複体からの射が定める零次の類は、値の複体について自然。 -/
lemma unitClass_naturality (g : K ⟶ L) (a : 𝟙_ (Complex A) ⟶ K) :
    homologyMap g 0 (_root_.SerrePositivity.HomologyZero.unitClass K a) = _root_.SerrePositivity.HomologyZero.unitClass L (a ≫ g) := by
  let x := cycleFromUnit K a
  let y := cycleFromUnit L (a ≫ g)
  have hy : cyclesMap g 0 ((actualCycles K).hom x) = (actualCycles L).hom y := by
    apply (ModuleCat.mono_iff_injective (L.iCycles 0)).mp inferInstance
    calc
      _ = g.f 0 (K.iCycles 0 ((actualCycles K).hom x)) :=
        congrArg (fun m => m ((actualCycles K).hom x)) (cyclesMap_i g 0)
      _ = g.f 0 x.val := congrArg (g.f 0) (congrArg (fun m => m x) (actualCycles_i K))
      _ = y.val := (cycleFromUnit_postcomp a g).symm
      _ = _ := (congrArg (fun m => m y) (actualCycles_i L)).symm
  change homologyMap g 0 ((ModuleCat.ofHom (_root_.SerrePositivity.HomologyZero.classMap K)) x) =
    (ModuleCat.ofHom (_root_.SerrePositivity.HomologyZero.classMap L)) y
  rw [← actualCycles_π, ← actualCycles_π]
  change homologyMap g 0 (K.homologyπ 0 ((actualCycles K).hom x)) =
    L.homologyπ 0 ((actualCycles L).hom y)
  have h : homologyMap g 0 (K.homologyπ 0 ((actualCycles K).hom x)) =
      L.homologyπ 0 (cyclesMap g 0 ((actualCycles K).hom x)) :=
    congrArg (fun m => m ((actualCycles K).hom x)) (homologyπ_naturality g 0)
  rwa [hy] at h

end SerrePositivity.EInfinity.HomologyZero

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers

variable {A : Type u} [CommRing A] {X Y : (operad A).Algebra}

@[reassoc]
private lemma homologyOperation_naturality (g : X ⟶ Y) (n : ℕ) :
    TensorPowers.map g.hom n ≫ homologyOperation Y n = homologyOperation X n ≫ g.hom := by
  simp only [homologyOperation, Category.assoc, leftUnitor_inv_naturality_assoc]
  rw [whisker_exchange_assoc, g.comm, id_tensorHom]

private lemma homologyBinary_naturality (g : X ⟶ Y) :
    (g.hom ⊗ₘ g.hom) ≫ homologyBinary Y = homologyBinary X ≫ g.hom := by
  have hone : (oneIso X.carrier).inv ≫ TensorPowers.map g.hom 1 =
      g.hom ≫ (oneIso Y.carrier).inv := by
    apply (cancel_mono (oneIso Y.carrier).hom).1
    rw [Category.assoc, oneIso_naturality]
    simp
  simp only [homologyBinary, Category.assoc, ← homologyOperation_naturality]
  have h : (g.hom ⊗ₘ g.hom) ≫ (Y.carrier ◁ (oneIso Y.carrier).inv) =
      (X.carrier ◁ (oneIso X.carrier).inv) ≫
        (g.hom ⊗ₘ TensorPowers.map g.hom 1) := by
    rw [tensorHom_comp_whiskerLeft, whiskerLeft_comp_tensorHom, hone]
  rw [reassoc_of% h]
  rfl

/-- 厳密代数の射は Berger–Fresse §1 の零次の単位を保つ。 -/
lemma homologyOne_naturality (g : X ⟶ Y) :
    homologyMap g.hom 0 (homologyOne X) = homologyOne Y := by
  rw [homologyOne, HomologyZero.unitClass_naturality, ← homologyOperation_naturality]
  change _root_.SerrePositivity.HomologyZero.unitClass Y.carrier (𝟙 _ ≫ homologyOperation Y 0) =
    _root_.SerrePositivity.HomologyZero.unitClass Y.carrier (homologyOperation Y 0)
  exact congrArg (_root_.SerrePositivity.HomologyZero.unitClass Y.carrier) (Category.id_comp _)

/-- 厳密代数の射は Berger–Fresse §1 の零次の積を保つ。 -/
lemma homologyProduct_naturality (g : X ⟶ Y) (x y : X.carrier.homology 0) :
    homologyMap g.hom 0 (_root_.SerrePositivity.HomologyZero.pairingValue (homologyBinary X) x y) =
      _root_.SerrePositivity.HomologyZero.pairingValue (homologyBinary Y) (homologyMap g.hom 0 x)
        (homologyMap g.hom 0 y) := by
  obtain ⟨a, rfl⟩ := _root_.SerrePositivity.HomologyZero.unitClass_surjective X.carrier x
  obtain ⟨b, rfl⟩ := _root_.SerrePositivity.HomologyZero.unitClass_surjective X.carrier y
  simp only [_root_.SerrePositivity.HomologyZero.pairingValue_class, HomologyZero.unitClass_naturality]
  congr 1
  simp only [_root_.SerrePositivity.HomologyZero.unitPairing, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Category.assoc, ← homologyBinary_naturality, ← tensorHom_comp_tensorHom_assoc]

/-- 厳密代数の H⁰ を、Berger–Fresse §1 の可換代数として取る関手。 -/
def homologyAlgebraFunctor (A : Type u) [CommRing A] :
    (operad A).Algebra ⥤ CommAlgCat.{u} A where
  obj := homologyCommAlgebra
  map {X Y} g := by
    let := homologyCommRing X
    let := homologyCommRing Y
    let := homologyAlgebra X
    let := homologyAlgebra Y
    exact CommAlgCat.ofHom
      { toFun := homologyMap g.hom 0
        map_zero' := map_zero (homologyMap g.hom 0).hom
        map_add' := map_add (homologyMap g.hom 0).hom
        map_one' := homologyOne_naturality g
        map_mul' := homologyProduct_naturality g
        commutes' := fun r => by
          change homologyMap g.hom 0 (algebraMap A (X.carrier.homology 0) r) =
            algebraMap A (Y.carrier.homology 0) r
          rw [homologyAlgebra_algebraMap, homologyAlgebra_algebraMap,
            ← homologyOne_naturality g]
          exact (homologyMap g.hom 0).hom.map_smul r _ }
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    change homologyMap (𝟙 X.carrier) 0 x = x
    rw [homologyMap_id]
    rfl
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro x
    change homologyMap (g.hom ≫ h.hom) 0 x = homologyMap h.hom 0 (homologyMap g.hom 0 x)
    rw [homologyMap_comp]
    rfl

/-- 厳密な H⁰ の関手は擬同型を可換代数の同型に送る。 -/
lemma homologyAlgebraFunctor_map_isIso (g : X ⟶ Y) [QuasiIso g.hom] :
    IsIso ((homologyAlgebraFunctor A).map g) := by
  have h : Function.Bijective ((homologyAlgebraFunctor A).map g) :=
    ConcreteCategory.bijective_of_isIso (homologyMap g.hom 0)
  exact (ConcreteCategory.isIso_iff_bijective ((homologyAlgebraFunctor A).map g)).mpr h

end SerrePositivity.EInfinity.BarrattEccles
