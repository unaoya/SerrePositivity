module
public import SerrePositivity.InfinityCategories.Derived.DGKernelSourceGraphBimoduleIso
public import SerrePositivity.DifferentialGraded.Tensor.Triple
/-!
概要：元の導来 kernel の raw factor と augmentation の任意射自然性を照合する。
方針：同じ比較と実射作用を保ち、全前合成・同じ指定切断上の四角形を使う。
規約：後続 kernel の平坦性・射の可逆性を要求しない。使われ方：元の κ の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (C D E : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  [DGCategory R E] [Small.{u} E] (F : DGFunctor R C D)
omit [Small.{u} C] in
lemma dgKernelSourceGraphBimoduleIso_hom_naturality
    {P0 P1 : BimoduleCategory R E D} (g : P0 ⟶ P1) :
    BimoduleTensor.composeMap R E D C g
        (𝟙 (BimoduleCategory.of R D C (functorGraph R C D F))) ≫
      (dgKernelSourceGraphBimoduleIso R C D E F
        (BimoduleCategory.underlying R E D P1)).hom =
    (dgKernelSourceGraphBimoduleIso R C D E F
        (BimoduleCategory.underlying R E D P0)).hom ≫
      (BimoduleCategory.middleLeftRestrictionFunctor R E D C F).map g := by
  let U := BimoduleCategory.of R D D (Bimodule.diagonal R D)
  let L := BimoduleCategory.middleLeftRestrictionFunctor R E D C F
  let a0 := BimoduleTensor.composeLeftRestrictionIso R E D D C F P0 U
  let a1 := BimoduleTensor.composeLeftRestrictionIso R E D D C F P1 U
  let u0 := BimoduleTensor.rightBimoduleUnitIso R E D
    (BimoduleCategory.underlying R E D P0)
  let u1 := BimoduleTensor.rightBimoduleUnitIso R E D
    (BimoduleCategory.underlying R E D P1)
  have ha := BimoduleTensor.composeLeftRestrictionIso_naturality R E D D C F g (𝟙 U)
  rw [CategoryTheory.Functor.map_id] at ha
  have hu := congrArg (fun z => L.map z)
    (BimoduleTensor.rightBimoduleUnitIso_naturality R E D g)
  simp only [CategoryTheory.Functor.map_comp] at hu
  change _ ≫ (a1 ≪≫ L.mapIso u1).hom = (a0 ≪≫ L.mapIso u0).hom ≫ _
  simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom]
  calc
    _ = (BimoduleTensor.composeMap R E D C g
        (𝟙 (BimoduleCategory.of R D C (functorGraph R C D F))) ≫ a1.hom) ≫
        L.map u1.hom := (Category.assoc _ _ _).symm
    _ = (a0.hom ≫ L.map (BimoduleTensor.composeMap R E D D g (𝟙 U))) ≫
        L.map u1.hom := congrArg (fun z => z ≫ L.map u1.hom) ha
    _ = a0.hom ≫ (L.map (BimoduleTensor.composeMap R E D D g (𝟙 U)) ≫
        L.map u1.hom) := Category.assoc _ _ _
    _ = a0.hom ≫ (L.map u0.hom ≫ L.map g) := congrArg (fun z => a0.hom ≫ z) hu
    _ = _ := (Category.assoc _ _ _).symm
end SerrePositivity.InfinityCategories
