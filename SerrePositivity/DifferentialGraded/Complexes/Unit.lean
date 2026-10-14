module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-! # 単位からの射と閉次数零の元 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

/-- 複体 K の次数零の cycle の A 部分加群。 -/
abbrev zeroCycles (K : Complex A) := LinearMap.ker (K.d 0 1).hom

/-- 閉次数零の元から単位複体を始域とする射を構成する。 -/
def unitFromCycle (K : Complex A) (c : zeroCycles K) : 𝟙_ (Complex A) ⟶ K :=
  mkHomFromSingle (ModuleCat.ofHom
    { toFun a := a • c.val
      map_add' a b := add_smul a b _
      map_smul' a b := mul_smul a b _ }) (by
    intro j hj
    obtain rfl : j = 1 := by simpa using hj.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (K.d 0 1).hom (a • c.val) = 0
    rw [map_smul, c.property, smul_zero])

/-- 単位からの射の次数零成分を 1 に評価する。 -/
def cycleFromUnit (K : Complex A) (f : 𝟙_ (Complex A) ⟶ K) : zeroCycles K :=
  ⟨f.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1), by
    have hf := f.comm 0 1
    change f.f 0 ≫ K.d 0 1 =
      ((single (ModuleCat A) (.up ℤ) 0).obj (𝟙_ (ModuleCat A))).d 0 1 ≫ f.f 1 at hf
    rw [single_obj_d, zero_comp] at hf
    change (K.d 0 1).hom (f.f 0 _) = 0
    exact congr($(hf).hom ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1))⟩

/-- 構成後の評価は元の cycle を返す。 -/
@[simp]
lemma cycleFromUnit_unitFromCycle (K : Complex A) (c : zeroCycles K) :
    cycleFromUnit K (unitFromCycle K c) = c := by
  apply Subtype.ext
  change (unitFromCycle K c).f 0 (1 : A) = c.val
  dsimp only [unitFromCycle]
  rw [mkHomFromSingle_f]
  change (1 : A) • c.val = c.val
  exact one_smul A _

/-- 評価した cycle からの構成は元の射を返す。 -/
@[simp]
lemma unitFromCycle_cycleFromUnit (K : Complex A) (f : 𝟙_ (Complex A) ⟶ K) :
    unitFromCycle K (cycleFromUnit K f) = f := by
  apply from_single_hom_ext
  dsimp only [unitFromCycle]
  rw [mkHomFromSingle_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (show A from a) • f.f 0 (1 : A) = f.f 0 a
  simpa using ((f.f 0).hom.map_smul (show A from a) (1 : A)).symm

/-- Z⁰ の単位からの射と閉次数零の元は同値。 -/
def unitCycleEquiv (K : Complex A) : (𝟙_ (Complex A) ⟶ K) ≃ zeroCycles K where
  toFun := cycleFromUnit K
  invFun := unitFromCycle K
  left_inv := unitFromCycle_cycleFromUnit K
  right_inv := cycleFromUnit_unitFromCycle K
end SerrePositivity.DifferentialGraded

namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

/-- 単位からの射を結ぶホモトピーと Hom 複体の −1 境界は同じ関係。 -/
lemma unit_homotopy_iff (K : Complex A) (f g : 𝟙_ (Complex A) ⟶ K) :
    Nonempty (Homotopy f g) ↔
      ∃ h : CochainComplex.HomComplex.Cochain (𝟙_ (Complex A)) K (-1),
        CochainComplex.HomComplex.Cochain.ofHom f =
          CochainComplex.HomComplex.δ (-1) 0 h + CochainComplex.HomComplex.Cochain.ofHom g := by
  constructor
  · rintro ⟨h⟩
    exact ⟨_, ((CochainComplex.HomComplex.Cochain.equivHomotopy f g) h).property⟩
  · rintro ⟨h, dh⟩
    exact ⟨(CochainComplex.HomComplex.Cochain.equivHomotopy f g).symm ⟨h, dh⟩⟩
end SerrePositivity.DifferentialGraded
