module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanShapeIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap

/-!
概要：指定した形状同型の可換四角形は、元の標準右 Kan 錐の全写像を保つ。
方針：既存の coslice の後合成と引き戻しの射影の式を、普遍錐の uncurry へ渡す。
規約：元の始域・終域の同型と全錐を保ち、頂点の一致だけに置き換えない。
使われ方：Kerodon Definition 7.3.1.2（Tag 02Y9）、HTT 5.1.5.6 の指定右 Kan 変換の移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 固定図式の等号で移した同じ coslice の普遍錐の全写像は変わらない。
Kerodon Definition 7.3.1.2（Tag 02Y9）、既存の図式の等号による移送則。 -/
lemma sliceUnderUncurry_eqToHom {A K C : SSet.{u}} {p q : K ⟶ C}
    (h : p = q) (f : A ⟶ sliceUnder p) :
    sliceUnderUncurry (f ≫ eqToHom (congrArg sliceUnder h)) = sliceUnderUncurry f := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

/-- 底同型で移した同じ頂点の coslice の普遍錐は、全写像として後合成と一致する。
Kerodon Definition 7.3.1.2（Tag 02Y9）、既存の後合成と点表示の正規化の合成則。 -/
lemma pointCoslicePostIso_uncurry {A C C' : SSet.{u}} (b : C ≅ C')
    (v : C _⦋0⦌) (f : A ⟶ sliceUnder (SSet.yonedaEquiv.symm v)) :
    sliceUnderUncurry (f ≫ (pointCoslicePostIso b v).hom) = sliceUnderUncurry f ≫ b.hom := by
  dsimp only [pointCoslicePostIso, Iso.trans_hom, eqToIso.hom, sliceUnderPostcompIso]
  rw [← Category.assoc, sliceUnderUncurry_eqToHom (SSet.yonedaEquiv_symm_comp v b.hom),
    sliceUnderUncurry_postcomp]

/-- 同じ可換な形状同型の四角形は、標準右 Kan 錐の元の全写像を保持する。
Kerodon Definition 7.3.1.2（Tag 02Y9）、coslice の普遍錐と引き戻し射影の合成則。 -/
lemma rightKanShapeIsoOfSquare_canonical_val {K K' C C' D : SSet.{u}}
    (a : K ≅ K') (b : C ≅ C') {δ : K ⟶ C} {δ' : K' ⟶ C'}
    (hw : δ ≫ b.hom = a.hom ≫ δ') (F : C' ⟶ D) (v : C _⦋0⦌) :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (rightKanShapeIsoOfSquare a b hw v).hom ≫
      (rightKanCanonicalCone δ' F (b.hom.app (Opposite.op ⦋0⦌) v)).val =
    (rightKanCanonicalCone δ (b.hom ≫ F) v).val := by
  change _ ≫ (sliceUnderUncurry (pullback.fst _ _) ≫ F) = _
  rw [← Category.assoc, ← sliceUnderUncurry_precomp]
  have hp : (rightKanShapeIsoOfSquare a b hw v).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (pointCoslicePostIso b v).hom :=
    pullback.lift_fst _ _ _
  rw [hp, pointCoslicePostIso_uncurry]
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
