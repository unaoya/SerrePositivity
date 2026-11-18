module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorSourceSchur
public import SerrePositivity.EInfinity.BarrattEccles.Theory.ComplexCoproductHomotopy

/-!
# 二色係数比較を全 arity の Schur 複体へ束ねる

HA 3.2.4.7 の自由比較の複体の部分。各軌道の指定係数射を直和へ移す。
この鎖ホモトピー同値と厳密な Hopf 自由比較との一致は別に照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

/-- 二つの指定直和のテンソルを、指定二包含を保って二添字の直和にする。 -/
def tensorCoproductPairIso (F G : ℕ → Complex A) :
    (∐ F) ⊗ (∐ G) ≅ ∐ (fun p : ℕ × ℕ => F p.1 ⊗ G p.2) where
  hom := tensorCoproductDesc F G _
    (fun m n => Sigma.ι (fun p : ℕ × ℕ => F p.1 ⊗ G p.2) (m, n))
  inv := Sigma.desc (fun p => Sigma.ι F p.1 ⊗ₘ Sigma.ι G p.2)
  hom_inv_id := by
    apply tensorCoproduct_hom_ext
    intro m n
    simp only [← Category.assoc, tensorCoproductDesc_ι, Sigma.ι_comp_desc, Category.comp_id]
  inv_hom_id := by
    apply Sigma.hom_ext
    rintro ⟨m, n⟩
    simp only [Sigma.ι_comp_desc_assoc, tensorCoproductDesc_ι, Category.comp_id]

namespace BarrattEccles
variable (X Y : Complex A)

/-- 和の入力の実際の Schur 複体を、左右の入力数で添字づけた軌道直和へ運ぶ。 -/
def schurBinaryOrbitIso :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj (X ⊞ Y) ≅
      ∐ (fun p : ℕ × ℕ => orbitCoefficientComplex X Y (p.1 + p.2)
        (ULift.up ⟨p.1, by omega⟩)) :=
  schurComplexArityIso (sequence A) (X ⊞ Y) ≪≫ Sigma.mapIso (schurArityOrbitIso X Y) ≪≫
    sigmaSigmaIso (fun r : ℕ => ULift.{u} (Fin (r + 1))) (orbitCoefficientComplex X Y) ≪≫
    (Sigma.reindex binaryTensorCountIndexEquiv.symm
      (fun p => orbitCoefficientComplex X Y p.1 p.2)).symm

/-- 二つの Schur 複体のテンソルを、元の arity 成分の二添字直和へ同定する。 -/
def schurTensorArityIso :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj X ⊗ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj Y ≅
      ∐ (fun p : ℕ × ℕ =>
        arityCoinvariantComplex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A (sequence A) X) p.1 ⊗
          arityCoinvariantComplex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A (sequence A) Y) p.2) :=
  tensorIso (schurComplexArityIso (sequence A) X) (schurComplexArityIso (sequence A) Y) ≪≫
    tensorCoproductPairIso _ _

/-- 指定二色係数射を束ねて得る、自由 Schur 複体の鎖ホモトピー同値。 -/
def freeSchurCoefficientHomotopyEquiv :
    HomotopyEquiv ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj (X ⊞ Y))
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj X ⊗ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj Y) :=
  (HomotopyEquiv.ofIso (schurBinaryOrbitIso X Y)).trans
    ((complexCoproductHomotopyEquiv (A := A) (fun p : ℕ × ℕ =>
      orbitCoefficientComparisonEquiv X Y p.1 p.2)).trans
        (HomotopyEquiv.ofIso (schurTensorArityIso X Y).symm))

end BarrattEccles
end SerrePositivity.EInfinity
