module

public import SerrePositivity.InfinityCategories.F1.CoherentHomComparison

/-!
概要：豊穣 Hom から構成した coherent な単体の固定面と固定終点。
方針：先頭面の Hom の作用を豊穣恒等と比較し、最後の頂点を対象で評価する。
規約：Mathlib の包含順序に合わせた右 pinched 模型を用いる。
使われ方：Kerodon Construction 4.6.7.3、Remark 4.6.7.9、写像空間の比較射の各単体。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：比較の先頭面の Hom の作用は端点を合わせると豊穣恒等に定値。
方針：二つの castSucc の分岐を計算し、対象の等号による Hom の移送を打ち消す。
規約：最後の頂点へ至る Hom を含まない。
使われ方：Kerodon Construction 4.6.7.3、先頭面の定値性。 -/
lemma coherentHomComparisonHom_cast_cast {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) (i j : Fin (n + 1)) :
    coherentHomComparisonHom σ i.castSucc j.castSucc ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_cast X Y j)) =
      toUnit _ ≫ eId SSet X := by
  simp -implicitDefEqProofs +instances [coherentHomComparisonHom, coherentHomComparisonObj]

/-- 概要：定値な coherent nerve の単体は全対象を固定した恒等 Hom の豊穣関手。
方針：零単体の定義と定値単体の前合成を計算する。
規約：対象の作用と Hom の作用を同時に比較する。
使われ方：Kerodon Construction 4.6.7.3、先頭面の定値性の標的。 -/
lemma coherentNerveConstant_obj {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X : C) (n : ℕ) (i : SimplicialThickening (ULift.{u} (Fin (n + 1)))) :
    (PinchedHom.constant (coherentNerveVertex X) n).obj i = X := rfl

/-- 概要：定値な coherent nerve の単体の Hom の作用は豊穣恒等に定値。
方針：前合成した零単体の Hom の定義と終対象への射の一意性を使う。
規約：端点は全て同じ対象 X。
使われ方：Kerodon Construction 4.6.7.3、先頭面の Hom の比較。 -/
lemma coherentNerveConstant_map {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X : C) (n : ℕ) (i j : SimplicialThickening (ULift.{u} (Fin (n + 1)))) :
    (PinchedHom.constant (coherentNerveVertex X) n).map i j = toUnit _ ≫ eId SSet X := by
  change (_ ≫ toUnit _) ≫ eId SSet X = _
  rw [comp_toUnit]

/-- 概要：比較の coherent な単体の先頭面は始域の頂点に定値。
方針：対象上の castSucc の計算と、先頭面の Hom の作用の計算を使う。
規約：先頭面は PinchedHom.front n による制限。
使われ方：Kerodon Construction 4.6.7.3、右 pinched 単体の始域条件。 -/
lemma coherentHomComparisonSimplex_source {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    (SimplicialNerve C).map (PinchedHom.front n).op (coherentHomComparisonSimplex σ) =
      PinchedHom.constant (coherentNerveVertex X) n := by
  apply EnrichedFunctor.ext SSet (fun i ↦ coherentHomComparisonObj_cast X Y i.as.down)
  intro i j
  change (_ ≫ coherentHomComparisonHom σ i.as.down.castSucc j.as.down.castSucc) ≫
    eqToHom _ = (PinchedHom.constant (coherentNerveVertex X) n).map i j
  rw [Category.assoc, coherentHomComparisonHom_cast_cast, coherentNerveConstant_map,
    ← Category.assoc, comp_toUnit]

/-- 概要：比較の coherent な単体の最後の頂点は終域の頂点。
方針：coherent nerve の零単体を対象で評価して比較する。
規約：最後の頂点を PinchedHom.lastVertex n で選ぶ。
使われ方：Kerodon Construction 4.6.7.3、右 pinched 単体の終域条件。 -/
lemma coherentHomComparisonSimplex_target {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    (SimplicialNerve C).map (PinchedHom.lastVertex n).op (coherentHomComparisonSimplex σ) =
      coherentNerveVertex Y := by
  apply (coherentNerveVertexEquiv C).symm.injective
  change coherentHomComparisonObj X Y (Fin.last (n + 1)) = Y
  exact coherentHomComparisonObj_last X Y n

/-- 概要：豊穣 Hom の単体が定める coherent nerve の右 pinched 単体。
方針：構成した豊穣関手に固定面と固定終点の証明を添える。
規約：局所 Kan 性を仮定しない。
使われ方：Kerodon Construction 4.6.7.3、比較射の単体上の作用。 -/
noncomputable def coherentHomComparisonPinchedSimplex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n where
  val := coherentHomComparisonSimplex σ
  source := coherentHomComparisonSimplex_source σ
  target := coherentHomComparisonSimplex_target σ

end SerrePositivity.InfinityCategories
