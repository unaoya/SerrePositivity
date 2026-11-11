module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionLastVertexMap

/-!
# 二重細分の随伴と反復単位

概要：二重細分からの射を二回の Ex への射に転置し、反復最終頂点が反復単位になることを示す。
方針：sd⊣Ex の Hom 同値を合成し、単位の自然性を使う。
規約：Moss 2020 Proposition 21 の有限段階の充填の随伴による表示。
使われ方：二重細分の horn の境界条件を二回の Ex の単位へ移す。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory

/--
概要：二重細分からの射と二回の Ex への射の自然な同値。
方針：sd⊣Ex の Hom 同値を二回合成する。
規約：内側の細分を先に転置する。
使われ方：二重細分から horn への写像の転置。
-/
def doubleSubdivisionHomEquiv (X Y : SSet.{u}) :
    (SSet.sd.obj (SSet.sd.obj X) ⟶ Y) ≃ (X ⟶ SSet.ex.obj (SSet.ex.obj Y)) :=
  (SSet.sdExAdjunction.homEquiv _ _).trans (SSet.sdExAdjunction.homEquiv _ _)

/--
概要：二重細分の Hom 同値は元の単体集合からの前合成と可換である。
方針：一回の随伴の前合成の自然性を二回適用する。
規約：二重細分された horn の包含の転置の式。
使われ方：境界の等式を Ex への射の等式へ移す。
-/
theorem doubleSubdivisionHomEquiv_naturality_left {X X' Y : SSet.{u}}
    (f : X' ⟶ X) (g : SSet.sd.obj (SSet.sd.obj X) ⟶ Y) :
    doubleSubdivisionHomEquiv X' Y (SSet.sd.map (SSet.sd.map f) ≫ g) =
      f ≫ doubleSubdivisionHomEquiv X Y g := by
  simp only [doubleSubdivisionHomEquiv, Equiv.trans_apply,
    SSet.sdExAdjunction.homEquiv_naturality_left]

/--
概要：反復最終頂点の転置は Ex の単位の二回の合成である。
方針：随伴の後合成の自然性と、Ex の単位の自然性を使う。
規約：Moss 2020 Proposition 21 の有限段階の遷移との整合。
使われ方：horn の恒等写像を二回の Ex で充填する。
-/
theorem doubleSubdivisionHomEquiv_lastVertex (X : SSet.{u}) :
    doubleSubdivisionHomEquiv X X
      (subdivisionLastVertexMap.app (SSet.sd.obj X) ≫ subdivisionLastVertexMap.app X) =
      exUnitAt X ≫ exUnitAt (SSet.ex.obj X) := by
  change (SSet.sdExAdjunction.homEquiv X (SSet.ex.obj X))
    ((SSet.sdExAdjunction.homEquiv (SSet.sd.obj X) X)
      (subdivisionLastVertexMap.app (SSet.sd.obj X) ≫ subdivisionLastVertexMap.app X)) = _
  rw [SSet.sdExAdjunction.homEquiv_naturality_right]
  simp only [subdivisionLastVertexMap, Functor.id_obj, Equiv.apply_symm_apply]
  rw [← exUnitAt_naturality]
  rw [SSet.sdExAdjunction.homEquiv_naturality_right]
  simp only [Equiv.apply_symm_apply]
  exact (exUnitAt_naturality (exUnitAt X)).symm

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
