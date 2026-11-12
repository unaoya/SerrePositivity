module
public import SerrePositivity.DifferentialGraded.Bimodule.Value

/-!
概要：同じ原 kernel へ増大する模型の比較は、直接選択と二段合成で一致する。
方針：実 augmentation の二合成から準同型性を回収し、指定比較の選択独立性を使う。
規約：指定比較を再選択しない。使われ方：一般 cell 模型の合成整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D C E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R C] [Small.{u} C]
  [DGCategory R E] [Small.{u} E] (F : DGFunctor R C E)
omit [Small.{u} D] in
lemma dgKernelTargetModel_map_quasiIso
    {P : BimoduleCategory R E D} {Q Q' : BimoduleCategory R C D}
    (q : Q ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q' : Q' ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (b : Q ⟶ Q') (h : b ≫ q' = q)
    (hq : BimoduleCategory.quasiIso R C D q)
    (hq' : BimoduleCategory.quasiIso R C D q') :
    BimoduleCategory.quasiIso R C D b :=
  (BimoduleCategory.quasiIso R C D).of_postcomp b q' hq' (by rw [h]; exact hq)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
