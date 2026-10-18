module
public import SerrePositivity.InfinityCategories.Stable.LeftFibrationInitialChoice
public import SerrePositivity.InfinityCategories.Stable.CoconeMappingPiZeroNaturality

/-! # 余極限余錐の変更と余錐空間の Hom 表示

概要：余極限余錐を取り替えると Hom 表示は標準頂点比較による前合成で変わる。
方針：coslice 射影に始対象変更の公式を適用し、形状制限との自然性と合成する。
規約：異なる図式そのものの比較は含めない。使われ方：二枝交換後の余錐の選択の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：二つの余極限余錐による Hom 表示は標準の頂点比較同型による前合成で一致する。
方針：coslice の二つの始対象に対する公式を使う。
規約：図式と終点を固定する。使われ方：余極限余錐の選択変更。 -/
lemma coconeMappingSpacePiZeroEquiv_change_cocone {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c d : JoinCocone p) (hc : IsColimitCone c) (hd : IsColimitCone d)
    (y : X _⦋0⦌) (a : SSet.π₀ (coconeMappingSpace p y)) :
    (colimitVertexIso c d hc hd).hom ≫ coconeMappingSpacePiZeroEquiv d hd y a =
      coconeMappingSpacePiZeroEquiv c hc y a :=
  leftFibrationInitialFiberPiZeroEquiv_change_initial (sliceUnderProjection p) c d hc hd y a

/-- 概要：形状制限後の余極限余錐を任意に選んでも Hom 表示は標準比較と可換。
方針：制限した余錐との自然性と、同じ図式の余極限余錐の変更の公式を合成する。
規約：元の余錐・制限余錐・新たな余錐の余極限性を明示する。
使われ方：交換した余錐から選択済みの懸垂表示へ移る準備。 -/
lemma coconeMappingSpacePiZeroEquiv_restrict_change_cocone
    {K L X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : JoinCocone p) (hc : IsColimitCone c) (i : L ⟶ K)
    (hi : IsColimitCone (c.restrict i)) (d : JoinCocone (i ≫ p)) (hd : IsColimitCone d)
    (y : X _⦋0⦌) (a : SSet.π₀ (coconeMappingSpace p y)) :
    eqToHom (congrArg (fun x => (SSet.HomotopyCategory.mk x : hoFunctor.obj X))
      (c.vertex_restrict i).symm) ≫ (colimitVertexIso (c.restrict i) d hi hd).hom ≫
        coconeMappingSpacePiZeroEquiv d hd y
          (SSet.mapπ₀ (cosliceRestrictionFiberMap p i y) a) =
      coconeMappingSpacePiZeroEquiv c hc y a := by
  rw [coconeMappingSpacePiZeroEquiv_change_cocone]
  exact coconeMappingSpacePiZeroEquiv_restrict c hc i hi y a

/-- 概要：二枝交換後の任意の余極限余錐での Hom 表示は、標準比較と交換作用に両立する。
方針：交換同型による制限余錐の余極限性を、制限と余錐変更の公式へ与える。
規約：新たな余錐は交換後の同じ図式のもの。使われ方：懸垂の交換作用の選択比較。 -/
lemma coconeMappingSpacePiZeroEquiv_spanSwap_change_cocone
    {X : SSet.{u}} [Quasicategory X] {p : (horn 2 0 : SSet.{u}) ⟶ X}
    (c : JoinCocone p) (hc : IsColimitCone c) (d : JoinCocone (spanSwap ≫ p))
    (hd : IsColimitCone d) (y : X _⦋0⦌) (a : SSet.π₀ (coconeMappingSpace p y)) :
    eqToHom (congrArg (fun x => (SSet.HomotopyCategory.mk x : hoFunctor.obj X))
      (c.vertex_restrict spanSwap).symm) ≫
        (colimitVertexIso (c.restrict spanSwap) d
          ((isColimitCone_iff_restrict_of_isIso c spanSwapIso.hom).1 hc) hd).hom ≫
          coconeMappingSpacePiZeroEquiv d hd y
            (SSet.mapπ₀ (cosliceRestrictionFiberMap p spanSwap y) a) =
      coconeMappingSpacePiZeroEquiv c hc y a :=
  coconeMappingSpacePiZeroEquiv_restrict_change_cocone c hc spanSwap
    ((isColimitCone_iff_restrict_of_isIso c spanSwapIso.hom).1 hc) d hd y a

end SerrePositivity.InfinityCategories
