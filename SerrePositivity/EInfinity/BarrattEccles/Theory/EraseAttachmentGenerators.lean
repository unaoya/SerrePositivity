module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseCellAttachment
public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseFreeGenerators
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellularGenerators

/-!
# 微分を消したセル付加の指定生成元

## 概要
Berger–Moerdijk 命題 4.1 の付加生成元を、微分消去後の自由生成元で比較する。

## 方針
自由代数の比較の随伴対応と、disk の分裂の次数ごとの式を使う。

## 規約
disk の下の生成元の像を取り、元の代数の元として比較する。

## 使われ方
セル段の自由表示の生成元の微分を、実際の付加の境界へ結びつける。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits HomologicalComplex HomotopicalAlgebra DifferentialGraded
open CochainComplex HomComplex MonoidalCategory
variable {A : Type u} [CommRing A]

/-- The erased disk section at the generator degree is its specified graded section. -/
lemma erasedDiskSphereSplitting_s_f (n : ℤ) :
    (erasedDiskSphereSplitting A n).s.f n =
      (singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).hom ≫ (complexDiskX₀ A n).inv := by
  change (complexDiskGradedSection A n).v n n (add_zero n) = _
  simp only [complexDiskGradedSection, Cochain.single_v]

namespace Operad
variable {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} {X Y : P.Algebra} {f : X ⟶ Y}
  (c : AttachCells.{u} (fun n => P.freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- Reindexing the erased attachment changes its cell by the inverse free comparison. -/
lemma eraseAttachment_cell (i : c.ι) :
    (P.eraseAttachment c).cell i =
      P.eraseFreeAlgebraIso.inv.app (complexDisk A (c.π i)) ≫ P.eraseAlgebra.map (c.cell i) := by
  change (P.eraseFreeAlgebraIso.inv.app (complexDisk A (c.π i)) ≫
    P.eraseAlgebra.map (c.cofan₂.inj i)) ≫ P.eraseAlgebra.map c.g₂ = _
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl

/-- The erased free generator has the original cell's free adjoint as its disk component. -/
lemma eraseAttachment_generator_homEquiv (i : c.ι) :
    P.erase.freeAlgebraAdjunction.homEquiv _ _
      (P.erase.freeAlgebraFunctor.map (erasedDiskSphereSplitting A (c.π i)).s ≫
        (P.eraseAttachment c).cell i) =
      (erasedDiskSphereSplitting A (c.π i)).s ≫
        (eraseDifferential A).map (P.freeAlgebraAdjunction.homEquiv _ _ (c.cell i)) := by
  rw [Adjunction.homEquiv_naturality_left, eraseAttachment_cell]
  erw [P.eraseFreeAlgebraIso_homEquiv]

/-- Evaluating the erased free generator gives exactly the actual attached generator. -/
lemma eraseAttachment_generator_value (i : c.ι) :
    (P.erase.freeAlgebraAdjunction.homEquiv _ _
      (P.erase.freeAlgebraFunctor.map (erasedDiskSphereSplitting A (c.π i)).s ≫
        (P.eraseAttachment c).cell i)).f (c.π i)
      ((singleObjXSelf (.up ℤ) (c.π i) (𝟙_ (ModuleCat A))).inv (1 : A)) =
      attachedGenerator c i := by
  rw [eraseAttachment_generator_homEquiv]
  let u := (singleObjXSelf (.up ℤ) (c.π i) (𝟙_ (ModuleCat A))).inv (1 : A)
  have hu : (singleObjXSelf (.up ℤ) (c.π i) (𝟙_ (ModuleCat A))).hom u = (1 : A) := by
    change ((singleObjXSelf (.up ℤ) (c.π i) (𝟙_ (ModuleCat A))).inv ≫
      (singleObjXSelf (.up ℤ) (c.π i) (𝟙_ (ModuleCat A))).hom) (1 : A) = 1
    rw [Iso.inv_hom_id]
    rfl
  change (P.freeAlgebraAdjunction.homEquiv _ _ (c.cell i)).f (c.π i)
    ((erasedDiskSphereSplitting A (c.π i)).s.f (c.π i) u) = _
  rw [erasedDiskSphereSplitting_s_f]
  change (P.freeAlgebraAdjunction.homEquiv _ _ (c.cell i)).f (c.π i)
    ((complexDiskX₀ A (c.π i)).inv
      ((singleObjXSelf (.up ℤ) (c.π i) (𝟙_ (ModuleCat A))).hom u)) = _
  rw [hu]
  rfl

end Operad
end SerrePositivity.EInfinity
