module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EdgewisePiComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.PiPathRelation
/-!
概要：全基点の反転 π 比較は、元の Kan 射と可換する。
方針：同じ定値解像基点上の両端射影の厳密な自然性を使う。
規約：元の実射と基点を保持し、任意の同値を選び直さない。
使われ方：反転した線形 Hom のホモロジーチャートの脚自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open SerrePositivity.KST.Spectra
open scoped Simplicial

/-- 共通解像から反転空間への、同じ定値基点を保つ π 同型。 -/
def dgBarCompactEdgewiseLeftPiEquiv (X : SSet.{u}) [KanComplex X] (n : ℕ) (x : X _⦋0⦌) :=
  KanHomotopyGroup.equivOfPiIsomorphism n (edgewiseLeft X)
    (HomotopyLimits.kanPiIsomorphism_of_homotopyEquivalence (edgewiseLeft X)
      (isQCatEquivalence_of_trivialKanFibration (edgewiseLeft X)).isSimplicialHomotopyEquivalence)
    (dgBarCompactEdgewiseVertex_left x)

/-- 共通解像から元の空間への、同じ定値基点を保つ π 同型。 -/
def dgBarCompactEdgewiseRightPiEquiv (X : SSet.{u}) [KanComplex X] (n : ℕ) (x : X _⦋0⦌) :=
  KanHomotopyGroup.equivOfPiIsomorphism n (edgewiseRight X)
    (HomotopyLimits.kanPiIsomorphism_of_homotopyEquivalence (edgewiseRight X)
      (isQCatEquivalence_of_trivialKanFibration (edgewiseRight X)).isSimplicialHomotopyEquivalence)
    (dgBarCompactEdgewiseVertex_right x)

lemma dgBarCompactOppositePiEquiv_naturality {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) (n : ℕ) (x : X _⦋0⦌)
    (a : KanHomotopyGroup X.op n (SSet.opObjEquiv.symm x)) :
    dgBarCompactOppositePiEquiv Y n (f.app _ x)
      (KanHomotopyGroup.map (x := SSet.opObjEquiv.symm x)
        (y := SSet.opObjEquiv.symm (f.app _ x)) (SSet.opFunctor.map f) rfl a) =
    dgBarCompactPiMap n f x (dgBarCompactOppositePiEquiv X n x a) := by
  let LX := dgBarCompactEdgewiseLeftPiEquiv X n x
  let LY := dgBarCompactEdgewiseLeftPiEquiv Y n (f.app _ x)
  let RX := dgBarCompactEdgewiseRightPiEquiv X n x
  let RY := dgBarCompactEdgewiseRightPiEquiv Y n (f.app _ x)
  obtain ⟨a₀, rfl⟩ := LX.surjective a
  have hL := KanHomotopyGroup.map_square (d := SSet.opObjEquiv.symm (f.app _ x))
    (edgewiseSubdivisionMap f) (SSet.opFunctor.map f)
    (edgewiseLeft X) (edgewiseLeft Y) (edgewiseLeft_naturality f)
    (dgBarCompactEdgewiseVertex_map f x) rfl (dgBarCompactEdgewiseVertex_left x)
    (dgBarCompactEdgewiseVertex_left (f.app _ x)) n a₀
  have hL' : LY (KanHomotopyGroup.map (edgewiseSubdivisionMap f)
      (dgBarCompactEdgewiseVertex_map f x) a₀) =
        KanHomotopyGroup.map (x := SSet.opObjEquiv.symm x)
        (y := SSet.opObjEquiv.symm (f.app _ x)) (SSet.opFunctor.map f) rfl (LX a₀) := by
    dsimp only [LY, LX, dgBarCompactEdgewiseLeftPiEquiv]
    simp only [KanHomotopyGroup.equivOfPiIsomorphism_apply]
    exact hL
  have hR := KanHomotopyGroup.map_square (edgewiseSubdivisionMap f) f
    (edgewiseRight X) (edgewiseRight Y) (edgewiseRight_naturality f)
    (dgBarCompactEdgewiseVertex_map f x) rfl (dgBarCompactEdgewiseVertex_right x)
    (dgBarCompactEdgewiseVertex_right (f.app _ x)) n a₀
  have hR' : RY (KanHomotopyGroup.map (edgewiseSubdivisionMap f)
      (dgBarCompactEdgewiseVertex_map f x) a₀) = KanHomotopyGroup.map f rfl (RX a₀) := by
    simpa only [RY, RX, dgBarCompactEdgewiseRightPiEquiv,
      KanHomotopyGroup.equivOfPiIsomorphism_apply] using hR
  change RY (LY.symm (KanHomotopyGroup.map (x := SSet.opObjEquiv.symm x)
        (y := SSet.opObjEquiv.symm (f.app _ x)) (SSet.opFunctor.map f) rfl (LX a₀))) =
    KanHomotopyGroup.map f rfl (RX (LX.symm (LX a₀)))
  rw [← hL', MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  exact hR'

end SerrePositivity.InfinityCategories
