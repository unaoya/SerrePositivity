module

public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalColumns
public import SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveCechTupleAcyclic
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquareFunctor

/-!
概要：同じ射影F8四角形の実際の図式を、外方向の全複体へ渡す。
方針：既存の交代余面複体の関手と各列の完全性の判定を使う。
規約：元の各F8の全複体と全ての単体の射を保持するČech版。
使われ方：中心側の図式との比較に用いるF8の全複体。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology
universe u
local notation "up" => ComplexShape.up ℕ
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

/-- 同じF8の全複体の関手を、外方向の交代余面複体へ代入する。 -/
def schemePerfectCechTupleSquarePositiveDouble :
    CochainComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) ℕ :=
  (alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).obj
    (schemePerfectCechTupleSquareFunctor f g F q hq U p hp hR hS)

variable [IsNoetherianRing R] (I : Ideal R)
variable (fI : X ⟶ Spec (CommRingCat.of (R ⧸ I ^ 1)))
variable (FI : Arrow.mk fI ⟶ Arrow.mk g)
variable (hqI : FI.right = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1))))

set_option backward.isDefEq.respectTransparency false in
/-- 各項の同じF8の完全性を、実際の外方向の全複体へ渡すČech版。
BST13 Lemma 3.9・BS17 Lemma 4.6(i) の射影Čech四角形を各項に用いる。
分離的なスキームの準連接層ではアフィン被覆のČechと一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem DegreeOneProjectiveModel.perfectCechTupleSquarePositiveTotal_acyclic
    (m : DegreeOneProjectiveModel g) (H : IsPullback FI.left fI g FI.right)
    [Surjective g] [IsIso (g ∣_ affineCenterComplement I)]
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleSquarePositiveDouble fI g FI (Ideal.Quotient.mk (I ^ 1))
        hqI U p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))) up).Acyclic := by
  apply cechIntegerLiftTotal_acyclic_of_columns
  intro n
  exact m.perfectCechTupleSquare_acyclic I fI g FI hqI H p hp hR U hU hcU
    (SimplexCategory.mk n)

end SerrePositivity.AlgebraicGeometry
