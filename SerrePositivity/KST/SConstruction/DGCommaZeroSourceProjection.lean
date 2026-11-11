module
public import SerrePositivity.KST.SConstruction.DGCochainZeroTarget
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaHomExt

/-! # 比較側が実零である comma Hom の入力射影同型
概要：比較側 Hom と比較標的が実零なら、元の入力 Hom 射影は鎖同型となる。
方針：同じ二射影と零比較で逆射を構成し、全比較 cochain の零性で逆律を示す。
規約：準同型性より強い実同型。使われ方：gluing の右軸包含の全 Hom。
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
  (hB : IsZero (homObject R E X.replacement Y.replacement))
  (hT : IsZero (homObject R E X.replacement (F.obj Y.source)))

include hT in
/-- 元の入力恒等射と比較零射は、同じ比較 cochain 零の境界条件を満たす。 -/
lemma dgCommaZeroSource_boundary :
    δ (-1) 0 (0 : Cochain (homObject R C X.source Y.source)
      (homObject R E X.replacement (F.obj Y.source)) (-1)) +
    Cochain.ofHom (biprod.lift (𝟙 (homObject R C X.source Y.source))
      (0 : homObject R C X.source Y.source ⟶ homObject R E X.replacement Y.replacement) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y) = 0 := by
  rw [hT.eq_of_tgt (biprod.lift (𝟙 _) 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y) 0]
  simp

/-- 元の入力恒等射と実比較零射を持つ、同じ全 Hom への逆候補。 -/
def dgCommaZeroSourceInverse : homObject R C X.source Y.source ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift R C E F X Y _ (𝟙 _) 0 0
    (dgCommaZeroSource_boundary R C E F X Y hT)

/-- 比較側が実零のとき、元の入力射影を順射に持つ実鎖同型。 -/
def dgCommaZeroSourceIso :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ≅ homObject R C X.source Y.source where
  hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y
  inv := dgCommaZeroSourceInverse R C E F X Y hT
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R C E F X Y
    · dsimp only [dgCommaZeroSourceInverse]
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_source]
      simp only [Category.comp_id, Category.id_comp]
    · exact hB.eq_of_tgt _ _
    · exact (dgCochain_eq_zero_of_isZero_target hT (-1) _).trans
        (dgCochain_eq_zero_of_isZero_target hT (-1) _).symm
  inv_hom_id := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_source R C E F X Y _ _ _ _ _

end SerrePositivity.KST.SConstruction
