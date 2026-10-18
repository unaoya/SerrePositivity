module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
概要：余単位が同型である始域からの Hom における右随伴の全単射性。
方針：余単位の自然性と三角恒等式で射を復元する。
規約：終域での余単位の同型性は要求しない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 のアフィン tilde の全層への随伴。
-/

@[expose] public section
noncomputable section
universe u v u' v'
open CategoryTheory
namespace SerrePositivity.KST.DerivedGeometry

/--
概要：余単位が同型である始域から任意の終域への射は右随伴の像から一意に復元できる。
方針：余単位の自然性で単射性を、逆余単位と単位の自然性で全射性を示す。
規約：二つの圏の任意の随伴について述べる。
使われ方：TT §3、Toën §3.2 の全層への tilde と大域切断の随伴。
-/
lemma adjunction_rightHom_bijective_of_counitIso
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) (M N : D) [IsIso (adj.counit.app M)] :
    Function.Bijective (G.map : (M ⟶ N) → (G.obj M ⟶ G.obj N)) := by
  constructor
  · intro f g h
    apply (cancel_epi (adj.counit.app M)).mp
    exact (adj.counit.naturality f).symm.trans
      ((congrArg (fun k => L.map k ≫ adj.counit.app N) h).trans (adj.counit.naturality g))
  · intro f
    refine ⟨inv (adj.counit.app M) ≫ L.map f ≫ adj.counit.app N, ?_⟩
    have hη : G.map (inv (adj.counit.app M)) = adj.unit.app (G.obj M) := by
      apply (cancel_mono (G.map (adj.counit.app M))).mp
      rw [← G.map_comp, IsIso.inv_hom_id, G.map_id, adj.right_triangle_components]
      rfl
    rw [G.map_comp, G.map_comp, hη]
    have hn := adj.unit.naturality f
    change f ≫ adj.unit.app (G.obj N) = adj.unit.app (G.obj M) ≫ G.map (L.map f) at hn
    rw [← Category.assoc, ← hn, Category.assoc, adj.right_triangle_components, Category.comp_id]

end SerrePositivity.KST.DerivedGeometry
