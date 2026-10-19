module
public import SerrePositivity.KST.SConstruction.ElementsResolution
public import SerrePositivity.KST.SConstruction.OppositeLabelledChains
public import SerrePositivity.KST.SConstruction.CoefficientCoproduct

/-! # 二重単体解消の転置行の余積表示
概要：底の射列を固定すると、残る単体集合は最後の対象の係数である。
方針：反対圏の射列を底の射列と最後のラベルに分ける。
規約：係数の同値を仮定しない実際の同型。使われ方：対象ごとの比較を対角へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 解消の転置した行は底の射列で添字付けた係数の余積。 -/
def elementsResolutionRowIso {J : Type u} [Category.{v} J]
    (F : J ⥤ SSet.{max u v}) (m : ℕ) :
    (elementsResolution F).flip.obj (Opposite.op ⦋m⦌) ≅
      coefficientCoproduct (fun c : ComposableArrows Jᵒᵖ m => F.obj (c.obj (Fin.last m)).unop) :=
  NatIso.ofComponents
    (fun n => (oppositeLabelledChainEquiv (F.flip.obj n) m).toIso)
    (by
      intro n l h
      apply ConcreteCategory.hom_ext
      intro c
      rfl)

/-- 係数比較は行の余積表示の下で各最後の係数の比較に一致する。 -/
lemma elementsResolutionRowIso_naturality {J : Type u} [Category.{v} J]
    {F G : J ⥤ SSet.{max u v}} (η : F ⟶ G) (m : ℕ) :
    ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type (max u v))).map
      (elementsResolutionMap η)).app (Opposite.op ⦋m⦌) ≫ (elementsResolutionRowIso G m).hom =
    (elementsResolutionRowIso F m).hom ≫
      coefficientCoproductMap
        (fun c : ComposableArrows Jᵒᵖ m => η.app (c.obj (Fin.last m)).unop) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro c
  rfl

/-- 対象ごとの局所化同型は解消の転置した各行で局所化同型になる。 -/
lemma elementsResolutionRowMap_localized_isIso {J : Type u} [Category.{v} J]
    {F G : J ⥤ SSet.{max u v}} (η : F ⟶ G)
    (hη : ∀ j, IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map (η.app j)))
    (m : ℕ) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type (max u v))).map
        (elementsResolutionMap η)).app (Opposite.op ⦋m⦌))) := by
  let Q := SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ
  have hc := coefficientCoproductMap_localized_isIso
    (fun c : ComposableArrows Jᵒᵖ m => η.app (c.obj (Fin.last m)).unop)
    (fun c => hη (c.obj (Fin.last m)).unop)
  have he := congrArg Q.map (elementsResolutionRowIso_naturality η m)
  rw [Q.map_comp, Q.map_comp] at he
  have : IsIso (Q.map
      (((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type (max u v))).map
        (elementsResolutionMap η)).app (Opposite.op ⦋m⦌)) ≫
      Q.map (elementsResolutionRowIso G m).hom) := he.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp this

/-- 対象ごとの局所化同型は二重単体解消の対角でも局所化同型になる。 -/
lemma elementsResolutionMap_diagonal_localized_isIso {J : Type u} [Category.{v} J]
    {F G : J ⥤ SSet.{max u v}} (η : F ⟶ G)
    (hη : ∀ j, IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map (η.app j))) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (SerrePositivity.BisimplicialModel.diagonal.map (elementsResolutionMap η))) := by
  exact SerrePositivity.BisimplicialModel.localized_diagonal_map
    ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type (max u v))).map
      (elementsResolutionMap η))
    (fun m => elementsResolutionRowMap_localized_isIso η hη m.unop.len)

end SerrePositivity.KST.SConstruction
