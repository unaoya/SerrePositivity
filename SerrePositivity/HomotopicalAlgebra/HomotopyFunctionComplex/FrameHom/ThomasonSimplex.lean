module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BarConstruction
public import Mathlib.CategoryTheory.Grothendieck

/-!
# bar の同じ射列から Grothendieck 全図式の射列へ

概要：Cat 値図式の nerve の bar の単体を、元の全図式の単体に送る。
方針：基底の第 j 頂点で fiber の第 j 頂点を取り、元の移送と fiber の射を合成。
規約：基底と fiber の対象・射を保持する。反転性は別途証明する。
使われ方：Low 定理1.6 の Thomason 比較の実際の単体と全作用素の照合。
-/

@[expose] public section
universe uD vD uC vC
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason

variable {D : Type uD} [Category.{vD} D] (G : D ⥤ Cat.{vC, uC})

/-- 元の Cat 値図式を各対象の nerve へ送る。 -/
abbrev nerveDiagram : D ⥤ SSet.{max uC vC} := G ⋙ nerveFunctor

/-- 元の各 fiber の n 射列をラベルとする図式。 -/
abbrev values (n : ℕ) : D ⥤ Type (max uC vC) :=
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveDiagram G).flip.obj (Opposite.op (SimplexCategory.mk n))

/-- 元の bar 単体を、同じ基底と対角 fiber 頂点を持つ全図式の射列へ送る。 -/
def simplex {n : ℕ} (e : ComposableArrows (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values G n).Elements n) :
    ComposableArrows (Grothendieck G) n where
  obj j := ⟨(e.obj j).obj, (e.obj j).val.obj j⟩
  map {i j} h :=
    { base := (e.map h).hom
      fiber := eqToHom (congrArg (fun q => q.obj i) (e.map h).map_val) ≫
        (e.obj j).val.map h }
  map_id i := by
    refine Grothendieck.ext _ _ (by
      change (e.map (𝟙 i)).hom = 𝟙 _
      rw [e.map_id]
      rfl) ?_
    simp only [(e.obj i).val.map_id, Category.comp_id,
        Grothendieck.id_fiber, eqToHom_trans]
  map_comp {i j k} h l := by
    refine Grothendieck.ext _ _ (by
      change (e.map (h ≫ l)).hom = (e.map h).hom ≫ (e.map l).hom
      rw [e.map_comp]
      rfl) ?_
    simp only [Grothendieck.comp_fiber, CategoryTheory.Functor.map_comp,
      eqToHom_map, Category.assoc]
    have hn : (G.map (e.map l).hom).toFunctor.map ((e.obj j).val.map h) ≫
        eqToHom (congrArg (fun q => q.obj j) (e.map l).map_val) =
      eqToHom (congrArg (fun q => q.obj i) (e.map l).map_val) ≫ (e.obj k).val.map h :=
      eqToHom_naturality
        (fun q : ComposableArrows (G.obj (e.obj k).obj) n => q.map h) (e.map l).map_val
    rw [reassoc_of% hn]
    simp only [← Category.assoc, eqToHom_trans]

/-- 全面・全退化の再添字と元の係数作用素で比較は可換。 -/
lemma simplex_operator {n m : ℕ} (e : ComposableArrows (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values G n).Elements n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.simplex G ((SimplexCategory.toCat.map θ).toFunctor ⋙ e ⋙
        ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveDiagram G).flip.map θ.op).mapElements) =
      (SimplexCategory.toCat.map θ).toFunctor ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.simplex G e := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason
