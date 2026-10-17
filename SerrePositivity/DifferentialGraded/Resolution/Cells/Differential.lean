module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundarySquare
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-! # 指定境界を持つ任意次数cell付加のHom微分

内部微分に全境界置換作用素を加える。二乗零は具体的に証明済みの作用素の性質から得る。
合成のLeibnizと主dg圏instanceは後続で構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

def attachedHom (x y : D) : Complex A :=
  perturbComplex (C.internalHom A D I x y) (C.replacement A D I x y)
    (C.replacement_closed A D I x y) (C.replacement_square_zero A D I x y)

lemma attachedHom_X (x y : D) (n : ℤ) :
    (C.attachedHom A D I x y).X n = (C.internalHom A D I x y).X n := rfl

lemma attachedHom_d (x y : D) (n : ℤ) :
    (C.attachedHom A D I x y).d n (n + 1) =
    (C.internalHom A D I x y).d n (n + 1) + (C.replacement A D I x y).v n (n + 1) rfl :=
  perturbComplex_d _ _ _ _ _

/-- 元のHomの包含は追加微分後もchain mapとなる。 -/
def originalHomInclusion (x y : D) : homObject A D x y ⟶ C.attachedHom A D I x y :=
  CochainComplex.ofHom (fun n => (C.originalHom A D I x y).f n) (fun n => by
    have hz : (C.originalHom A D I x y).f n ≫ (C.replacement A D I x y).v n (n + 1) rfl = 0 := by
      simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] using
        congrArg (fun f : Cochain (homObject A D x y) (C.internalHom A D I x y) 1 =>
          f.v n (n + 1) rfl) (C.replacement_originalHom A D I x y)
    rw [attachedHom_d, comp_add, hz, add_zero]
    exact (C.originalHom A D I x y).comm n (n + 1))

lemma originalHomInclusion_f (x y : D) (n : ℤ) :
    (C.originalHomInclusion A D I x y).f n = (C.originalHom A D I x y).f n := rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
