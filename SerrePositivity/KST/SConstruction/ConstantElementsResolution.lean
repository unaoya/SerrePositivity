module
public import SerrePositivity.KST.SConstruction.ElementsResolutionRows

/-! # 定値係数の解消と積
概要：定値係数の二重単体解消の対角を、底の nerve と係数の積として同定する。
方針：底の射列と最後のラベルを取り、逆射をラベル輸送で構成する。
規約：比較は実際の単体集合の同型。使われ方：単体積版 Quillen A の値域側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.MonoidalCategory SSet
open scoped Simplicial

/-- 定値係数の解消の対角を底の nerve と係数の積へ送る。 -/
def constantElementsResolutionComparison {J : Type u} [Category.{v} J]
    (Z : SSet.{max u v}) :
    SerrePositivity.BisimplicialModel.diagonal.obj
      (elementsResolution ((Functor.const J).obj Z)) ⟶ nerve Jᵒᵖ ⊗ Z where
  app n := ↾fun c => ⟨c ⋙ (Functor.Elements.π _).op, (c.obj (Fin.last n.unop.len)).unop.val⟩
  naturality {n l} h := by
    apply ConcreteCategory.hom_ext
    intro c
    apply Prod.ext
    · rfl
    · change Z.map h (c.obj (h.unop.toOrderHom (Fin.last l.unop.len))).unop.val =
        Z.map h (c.obj (Fin.last n.unop.len)).unop.val
      apply congrArg (Z.map h)
      exact (c.map (homOfLE (Fin.le_last
        (h.unop.toOrderHom (Fin.last l.unop.len))))).unop.map_val.symm

/-- 定値係数の解消の積への比較は各次数で全単射。 -/
lemma constantElementsResolutionComparison_bijective {J : Type u} [Category.{v} J]
    (Z : SSet.{max u v}) (n : SimplexCategoryᵒᵖ) :
    Function.Bijective ((constantElementsResolutionComparison (J := J) Z).app n) := by
  let e := oppositeLabelledChainEquiv
    (((Functor.const J).obj Z).flip.obj n) n.unop.len
  constructor
  · intro c d h
    apply e.injective
    exact Sigma.ext (congrArg Prod.fst h) (heq_of_eq (congrArg Prod.snd h))
  · rintro ⟨c, x⟩
    exact ⟨e.symm ⟨c, x⟩, congrArg
      (fun s : Σ c : ComposableArrows Jᵒᵖ n.unop.len, Z.obj n => (s.1, s.2))
      (e.apply_symm_apply ⟨c, x⟩)⟩

/-- 定値係数の解消の対角は底の nerve と係数の積に同型。 -/
def constantElementsResolutionIso {J : Type u} [Category.{v} J]
    (Z : SSet.{max u v}) :
    SerrePositivity.BisimplicialModel.diagonal.obj
      (elementsResolution ((Functor.const J).obj Z)) ≅ nerve Jᵒᵖ ⊗ Z := by
  have : IsIso (constantElementsResolutionComparison (J := J) Z) := by
    have (n : SimplexCategoryᵒᵖ) :
        IsIso ((constantElementsResolutionComparison (J := J) Z).app n) :=
      (CategoryTheory.isIso_iff_bijective _).mpr
        (constantElementsResolutionComparison_bijective Z n)
    exact NatIso.isIso_of_isIso_app _
  exact asIso (constantElementsResolutionComparison (J := J) Z)

end SerrePositivity.KST.SConstruction
