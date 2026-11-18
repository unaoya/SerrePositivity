module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolutionInitialLifting
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellAugmentation
public import SerrePositivity.DifferentialGraded.Algebras.ModelCategory
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
概要：native cell 分解を、E2 が構成した実 dg 代数モデルの cofibrant 置換として使う。
方針：実モデルを局所登録し、元の全射擬同型 LLP と augmentation の二性質を代入する。
規約：モデル構造の仮定入力や大域 instance は追加せず、元の cell 分解と射を保持する。
使われ方：実 AW right frame と導来写像空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

attribute [local instance] _root_.SerrePositivity.DGAlgebra.modelCategory

lemma cellResolution_isCofibrant : IsCofibrant (cellResolution R A) := by
  apply (cofibration_iff _).mpr
  rw [← MorphismProperty.llp_eq_of_wfs (cofibrations (Mon (Complex R)))
    (trivialFibrations (Mon (Complex R)))]
  intro X Y p hp
  exact cellResolution_initial_hasLiftingProperty R A initialIsInitial p hp.1 hp.2

lemma cellAugmentation_fibration : Fibration (cellAugmentation R A) :=
  ⟨cellAugmentation_surjective R A⟩

lemma cellAugmentation_weakEquivalence : WeakEquivalence (cellAugmentation R A) :=
  ⟨cellAugmentation_quasiIso R A⟩

lemma cellAugmentation_trivialFibration :
    trivialFibrations (Mon (Complex R)) (cellAugmentation R A) :=
  ⟨cellAugmentation_surjective R A, cellAugmentation_quasiIso R A⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
