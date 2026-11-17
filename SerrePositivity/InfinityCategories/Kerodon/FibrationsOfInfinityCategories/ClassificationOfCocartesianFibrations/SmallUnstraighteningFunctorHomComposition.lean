module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningFunctorHomComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningIsoHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorOverIsomorphism
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso
/-!
概要：指定した小さいunstraighteningのHom作用の合成則を、元の相対頂点で保持する。
方針：同じ縮小同型の共役式で大きい合成比較を反映し、実頂点の同型を降ろす。
規約：Kerodon Remark 5.6.2.18（Tag 0271）、HTT §3.3.2の合成則と宇宙移送の法則。
使われ方：5∞-1の残り第2項の証明分割、同じ指定分類比較を続ける計算。
-/

@[expose] public noncomputable section
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
/-- 同じ小さい射作用は、元のHomの合成を底上の同型まで保持する。 -/
lemma smallUnstraighteningFunctorHom_comp_iso {B : SSet.{u}}
    {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (a : FunctorHom F G) (b : FunctorHom G J) :
    Nonempty (VertexIso
      (relativeFunctorVertex (smallLeftUnstraighteningProjection J) (smallLeftUnstraighteningProjection F)
        (smallUnstraighteningFunctorHom (a ≫ b)) (smallUnstraighteningFunctorHom_projection _))
      (relativeFunctorVertex (smallLeftUnstraighteningProjection J) (smallLeftUnstraighteningProjection F)
        (smallUnstraighteningFunctorHom a ≫ smallUnstraighteningFunctorHom b)
        (by rw [Category.assoc, smallUnstraighteningFunctorHom_projection,
          smallUnstraighteningFunctorHom_projection]))) := by
  obtain ⟨eb⟩ := unstraighteningFunctorHom_comp_iso a b
  let U := SSet.uliftFunctor.{u + 1, u}
  let q := smallLeftUnstraighteningProjection J
  let p := smallLeftUnstraighteningProjection F
  let M : U.obj (relativeFunctorSpace q p) ≅
      relativeFunctorSpace (leftUnstraighteningProjection J) (leftUnstraighteningProjection F) :=
    smallLeftUnstraighteningRelativeFunctorIso F J
  have hm (v : smallLeftUnstraightening F ⟶ smallLeftUnstraightening J) (hv : v ≫ q = p) :
      M.hom.app (Opposite.op ⦋0⦌) (ULift.up (relativeFunctorVertex q p v hv)) =
      relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        (((smallLeftUnstraighteningIso F).inv ≫ U.map v) ≫ (smallLeftUnstraighteningIso J).hom)
        (by rw [Category.assoc,
          show (smallLeftUnstraighteningIso J).hom ≫ leftUnstraighteningProjection J = U.map q from
            (smallLeftUnstraighteningOverIso J).hom.w,
          Category.assoc, ← U.map_comp, hv,
          show (smallLeftUnstraighteningIso F).inv ≫ U.map p = leftUnstraighteningProjection F from
            (smallLeftUnstraighteningOverIso F).inv.w]) := by
    change (relativeFunctorOverIso (smallLeftUnstraighteningOverIso F)
      (smallLeftUnstraighteningOverIso J)).hom.app _
        ((uliftRelativeFunctorMap q p).app _ (ULift.up (relativeFunctorVertex q p v hv))) = _
    rw [uliftRelativeFunctorMap_vertex]
    exact relativeFunctorOverIso_vertex (smallLeftUnstraighteningOverIso F)
      (smallLeftUnstraighteningOverIso J) (U.map v) (by
        change U.map v ≫ U.map q = U.map p
        rw [← U.map_comp, hv])
  let l := smallUnstraighteningFunctorHom (a ≫ b)
  have hl : l ≫ q = p := smallUnstraighteningFunctorHom_projection _
  let r := smallUnstraighteningFunctorHom a ≫ smallUnstraighteningFunctorHom b
  have hr : r ≫ q = p := by
    dsimp only [r, q, p]
    rw [Category.assoc, smallUnstraighteningFunctorHom_projection, smallUnstraighteningFunctorHom_projection]
  have hlong : ((smallLeftUnstraighteningIso F).inv ≫ U.map l) ≫
      (smallLeftUnstraighteningIso J).hom = unstraighteningFunctorHom (a ≫ b) := by
    dsimp only [l]
    rw [Category.assoc, smallUnstraighteningFunctorHom_naturality,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hshort : U.map r ≫ (smallLeftUnstraighteningIso J).hom =
      (smallLeftUnstraighteningIso F).hom ≫ unstraighteningFunctorHom a ≫ unstraighteningFunctorHom b := by
    dsimp only [r]
    rw [U.map_comp, Category.assoc, smallUnstraighteningFunctorHom_naturality,
      ← Category.assoc, smallUnstraighteningFunctorHom_naturality, Category.assoc]
  have hshort' : ((smallLeftUnstraighteningIso F).inv ≫ U.map r) ≫
      (smallLeftUnstraighteningIso J).hom = unstraighteningFunctorHom a ≫ unstraighteningFunctorHom b := by
    rw [Category.assoc, hshort, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hvl : M.hom.app (Opposite.op ⦋0⦌) (ULift.up (relativeFunctorVertex q p l hl)) =
      relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        (unstraighteningFunctorHom (a ≫ b)) (unstraighteningFunctorHom_projection _) := by
    rw [hm]
    apply Subtype.ext
    exact congrArg functorVertex hlong
  have hvr : M.hom.app (Opposite.op ⦋0⦌) (ULift.up (relativeFunctorVertex q p r hr)) =
      relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        (unstraighteningFunctorHom a ≫ unstraighteningFunctorHom b)
        (by rw [Category.assoc, unstraighteningFunctorHom_projection, unstraighteningFunctorHom_projection]) := by
    rw [hm]
    apply Subtype.ext
    exact congrArg functorVertex hshort'
  let eu := (qCatEquivalenceOfIso M).isFullyFaithful.preimageVertexIso
    (eqToIso (congrArg HomotopyCategory.mk hvl) ≪≫ eb ≪≫
      (eqToIso (congrArg HomotopyCategory.mk hvr)).symm)
  exact ⟨downVertexIso eu⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
