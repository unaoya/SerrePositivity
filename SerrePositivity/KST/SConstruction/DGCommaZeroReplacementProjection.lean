module
public import SerrePositivity.KST.SConstruction.DGCochainZeroTarget
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaHomExt

/-! # 入力側が実零である comma Hom の比較対象射影同型
概要：入力 Hom と比較標的が実零なら、元の比較対象 Hom 射影は鎖同型となる。
方針：同じ零入力・比較恒等射と零 cochain で逆射を作り、全 Hom の逆律を示す。
規約：元の射影を保持。使われ方：gluing の実左軸の全 Hom 同型。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
  (hA : IsZero (homObject R C X.source Y.source))
  (hT : IsZero (homObject R E X.replacement (F.obj Y.source)))

include hT in
/-- 元の比較恒等射と入力零射は、同じ比較 cochain 零の境界条件を満たす。 -/
lemma dgCommaZeroReplacement_boundary :
    δ (-1) 0 (0 : Cochain (homObject R E X.replacement Y.replacement)
      (homObject R E X.replacement (F.obj Y.source)) (-1)) +
    Cochain.ofHom (biprod.lift
      (0 : homObject R E X.replacement Y.replacement ⟶ homObject R C X.source Y.source)
      (𝟙 (homObject R E X.replacement Y.replacement)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y) = 0 := by
  rw [hT.eq_of_tgt (biprod.lift 0 (𝟙 _) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y) 0]
  simp

/-- 元の比較恒等射と入力零射を持つ、同じ全 Hom への逆候補。 -/
def dgCommaZeroReplacementInverse : homObject R E X.replacement Y.replacement ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift R C E F X Y _ 0 (𝟙 _) 0
    (dgCommaZeroReplacement_boundary R C E F X Y hT)

/-- 入力側が実零のとき、元の比較対象射影を順射に持つ実鎖同型。 -/
def dgCommaZeroReplacementIso :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ≅ homObject R E X.replacement Y.replacement where
  hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y
  inv := dgCommaZeroReplacementInverse R C E F X Y hT
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R C E F X Y
    · exact hA.eq_of_tgt _ _
    · dsimp only [dgCommaZeroReplacementInverse]
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_replacement]
      simp only [Category.comp_id, Category.id_comp]
    · exact (dgCochain_eq_zero_of_isZero_target hT (-1) _).trans
        (dgCochain_eq_zero_of_isZero_target hT (-1) _).symm
  inv_hom_id := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_replacement R C E F X Y _ _ _ _ _

end SerrePositivity.KST.SConstruction
