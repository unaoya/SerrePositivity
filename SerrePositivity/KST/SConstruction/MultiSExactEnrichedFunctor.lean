module
public import SerrePositivity.KST.SConstruction.SExactParameterizedNaturality
public import SerrePositivity.KST.SConstruction.MultiSimplicial

/-! # 元の有限反復 S の全完全関手族への作用
概要：元の多単体図式の各値を、同じ全完全関手族を持つ厳密豊穣自己関手にする。
方針：元の多次数の値を保持し、各 S_n の全 Hom 作用を同じ順序で反復する。
規約：零反復も含む。使われ方：全方向の比較と反復 core・実現への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 完全関手の入力の同じ実安定値を、元の反復 S の入力として保持する。 -/
def stableCategoryModel (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : StableModel.{u} :=
  { carrier := C.obj }

/-- 元の多単体図式の同じ各値を、全完全関手族の安定対象として保持する。 -/
def multiSExactCategory (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} :=
  ⟨(multiSConstruction r (stableCategoryModel C)).obj d, inferInstance, inferInstance⟩

/-- 全完全関手族を、元の有限反復 S 間の全完全関手族へ送る。 -/
def multiSExactEnrichedMap : (r : ℕ) → (d : Fin r → SimplexCategoryᵒᵖ) →
    (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) → (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (multiSExactCategory r d C) (multiSExactCategory r d D) : SSet.{u})
  | 0, _, C, D => 𝟙 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u})
  | r + 1, d, C, D =>
      multiSExactEnrichedMap r (fun i => d i.succ) C D ≫
        sExactEnrichedMap (d 0).unop.len
          (multiSExactCategory r (fun i => d i.succ) C)
          (multiSExactCategory r (fun i => d i.succ) D)

/-- 同じ元の有限反復 S の値と全 Hom を保持する厳密豊穣自己関手。 -/
def multiSExactEnrichedEndofunctor (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} where
  obj := multiSExactCategory r d
  map := multiSExactEnrichedMap r d
  map_id C := by
    induction r with
    | zero => exact Category.comp_id _
    | succ r ih =>
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity C ≫ (multiSExactEnrichedMap r _ C C ≫ _) = _
      erw [← Category.assoc, ih]
      exact (sExactEnrichedEndofunctor (d 0).unop.len).map_id _
  map_comp C D E := by
    induction r with
    | zero =>
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition C D E ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition C D E
      simp only [id_tensorHom_id, Category.id_comp, Category.comp_id]
    | succ r ih =>
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition C D E ≫ (multiSExactEnrichedMap r _ C E ≫ _) = _
      erw [← Category.assoc, ih, Category.assoc,
        (sExactEnrichedEndofunctor (d 0).unop.len).map_comp]

/-- 元の完全射による反復作用を、同じ実完全射として保持する。 -/
def multiSExactMap (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (multiSExactCategory r d C) (multiSExactCategory r d D) := by
  let f : stableCategoryModel C ⟶ stableCategoryModel D :=
    ⟨F.hom, preservesCofiberData_of_isExactFunctor F.hom⟩
  let g := ((multiSEndofunctor r).obj d).map f
  exact ⟨g.val, ⟨g.property.1, fun t ht => g.property.2 t ht⟩⟩

/-- 全反復の豊穣作用は、通常の完全射で元の同じ反復作用を回収する。 -/
lemma multiSExactEnrichedEndofunctor_hom (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F ≫ (multiSExactEnrichedEndofunctor r d).map C D =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv (multiSExactMap r d F) := by
  induction r with
  | zero => exact Category.comp_id _
  | succ r ih =>
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F ≫ (multiSExactEnrichedMap r _ C D ≫ _) = _
    erw [← Category.assoc, ih]
    exact sExactEnrichedEndofunctor_hom (d 0).unop.len (multiSExactMap r _ F)

end SerrePositivity.KST.SConstruction
