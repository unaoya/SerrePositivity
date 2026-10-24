module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitLeftZigzag
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitHomComponentInjective
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise

/-!
概要：左 zigzag の単位による像の一致から各点での恒等性と全体の可逆性を得る。
方針：各頂点への制限に定値 Hom 比較の単射性を適用し、点ごとの可逆性判定を使う。
規約：各点での等式を h Fun 全体の等式とは扱わない。
使われ方：B1 の左三角恒等式の残る冪等性による判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単位比較の像が恒等と一致する自己変換は各点では恒等。
方針：零単体パラメータへの前合成を取り、定値 Hom 比較と定値化の単射性を使う。
規約：h Fun 全体で恒等であるとはまだ主張しない。
使われ方：左 zigzag の点ごとの可逆性。 -/
lemma UnitMappingSpaceCondition.component_eq_id_of_unitHomMap_eq
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : FunctorHom (𝟙 X) (F ≫ G)}
    (hη : UnitMappingSpaceCondition η) (L : FunctorHom F F)
    (hL : qcatUnitHomMap η (𝟙 X) F L =
      qcatUnitHomMap η (𝟙 X) F (𝟙 (HomotopyCategory.mk (functorVertex F))))
    (x : X _⦋0⦌) :
    functorHomEvaluate L x = 𝟙 (HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) x)) := by
  let A : SSet.{u} := Δ[0]
  let i : A ⟶ X := SSet.const x
  have hi : Function.Injective (qcatUnitHomMap η i (i ≫ F)) := by
    have aux (V : A ⟶ Y) (hV : V = SSet.const (F.app (Opposite.op ⦋0⦌) x)) :
        Function.Injective (qcatUnitHomMap η i V) := by
      subst V
      exact hη.qcatUnitHomMap_constant_injective x (F.app (Opposite.op ⦋0⦌) x)
    exact aux (i ≫ F) (SSet.const_comp x F)
  have hh : (hoFunctor.map ((pre i).app Y)).toFunctor.map L =
      (hoFunctor.map ((pre i).app Y)).toFunctor.map (𝟙 (HomotopyCategory.mk (functorVertex F))) := by
    apply hi
    exact (qcatUnitHomMap_precomp η i (𝟙 X) F L).trans
      ((congrArg ((hoFunctor.map ((pre i).app X)).toFunctor.map) hL).trans
        (qcatUnitHomMap_precomp η i (𝟙 X) F _).symm)
  rw [CategoryTheory.Functor.map_id] at hh
  apply constantFunctorHomMap_injective (A := A)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) _ _
  rw [← functorHomEvaluate_constantFunctorHomMap A L x,
    constantFunctorHomMap_id]
  change (constantFunctorCompIso A x F).inv ≫
    (hoFunctor.map ((pre i).app Y)).toFunctor.map L ≫
      (constantFunctorCompIso A x F).hom = _
  rw [hh]
  erw [Category.id_comp, Iso.inv_hom_id]

/-- 概要：単位比較の像が恒等と一致する自己変換は関手全体で可逆。
方針：各点での恒等性をホモトピー代表の可逆性へ移す。
規約：恒等性そのものへは強めない。
使われ方：左 zigzag の冪等性と組み合わせる最後の判定。 -/
lemma UnitMappingSpaceCondition.isIso_of_unitHomMap_eq
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : FunctorHom (𝟙 X) (F ≫ G)}
    (hη : UnitMappingSpaceCondition η) (L : FunctorHom F F)
    (hL : qcatUnitHomMap η (𝟙 X) F L =
      qcatUnitHomMap η (𝟙 X) F (𝟙 (HomotopyCategory.mk (functorVertex F)))) : IsIso L := by
  let H := functorHomHomotopy L
  have hv (x : X _⦋0⦌) :
      IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (simplicialHomotopyVertexEdge H x).toTruncated)
    rw [functorHomHomotopy_component, hη.component_eq_id_of_unitHomMap_eq L hL x]
    exact (inferInstance : IsIso (𝟙 (HomotopyCategory.mk
      (F.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj Y)))
  have hi := functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise H hv
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) at hi
  rw [functorHomHomotopy_hom] at hi
  exact hi

/-- 概要：各点の単位比較条件の下で構成した余単位の左 zigzag は可逆。
方針：右三角恒等式による像の一致に点ごとの単射性と可逆性判定を適用する。
規約：左三角恒等式への接続には冪等性をなお要する。
使われ方：指定単位と余単位の随伴データへの接続。 -/
lemma UnitMappingSpaceCondition.leftZigzag_isIso
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : FunctorHom (𝟙 X) (F ≫ G)}
    (hη : UnitMappingSpaceCondition η) (c : UnitCommaCounitData η) :
    IsIso (unitLeftZigzag η c.counitHom) :=
  hη.isIso_of_unitHomMap_eq _ c.leftZigzag_image

end SerrePositivity.InfinityCategories
