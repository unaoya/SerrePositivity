module

public import SerrePositivity.InfinityCategories.F1.CosliceRightRestriction
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap

/-!
概要：固定した辺からの錐の終点 fiber と終点への制限。
方針：coslice の制限が錐の可変部分を保つことを使い、充填を fiber 内へ戻す。
規約：辺を固定した coslice の終点 fiber は三角形の空間を表す。
使われ方：Kerodon Proposition 5.1.3.11、Proposition 5.1.6.7、cocartesian transport の写像空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：coslice の図式の制限は可変部分への射影を保つ。
方針：join の右包含の自然性で各錐を比較する。
規約：図式の射と単体集合は任意。
使われ方：Kerodon Proposition 5.1.3.11、三角形の終点の固定。 -/
lemma sliceUnderRestrict_projection {K L X : SSet.{u}} (e : K ⟶ X) (i : L ⟶ K) :
    sliceUnderRestrict e i ≫ sliceUnderProjection (i ≫ e) = sliceUnderProjection e := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInr L _ ≫ (joinMap i (𝟙 _) ≫ s.val)) =
    SSet.yonedaEquiv (joinInr K _ ≫ s.val)
  rw [← Category.assoc, joinInr_joinMap, Category.id_comp]

/-- 概要：図式の制限が錐の指定終点上の fiber に誘導する射。
方針：射影との可換性を使い、頂点 fiber の誘導射を取る。
規約：y は共通の終点。
使われ方：Kerodon Proposition 5.1.3.11、三角形の空間から写像空間への射。 -/
def cosliceRestrictionFiberMap {K L X : SSet.{u}} (e : K ⟶ X) (i : L ⟶ K)
    (y : X _⦋0⦌) : vertexFiber (sliceUnderProjection e) y ⟶
      vertexFiber (sliceUnderProjection (i ≫ e)) y :=
  vertexFiberMap _ _ (sliceUnderRestrict e i) (sliceUnderRestrict_projection e i) y

/-- 概要：coslice の自明な制限は終点を固定しても trivial Kan fibration。
方針：境界の図式を coslice で充填し、射影の可換性で終点の固定条件を戻す。
規約：制限射の充填性を仮定し、元の quasicategory 性は要求しない。
使われ方：Kerodon Proposition 5.1.3.11、写像空間の比較 span の射影。 -/
lemma cosliceRestrictionFiberMap_trivialKanFibration {K L X : SSet.{u}}
    (e : K ⟶ X) (i : L ⟶ K) [TrivialKanFibration (sliceUnderRestrict e i)]
    (y : X _⦋0⦌) : TrivialKanFibration (cosliceRestrictionFiberMap e i y) := by
  apply (trivialKanFibration_iff_boundary _).mpr
  intro n
  have := TrivialKanFibration.mem (p := sliceUnderRestrict e i) (boundary n).ι inferInstance
  constructor
  intro a b sq
  have hs : CommSq (a ≫ vertexFiberι (sliceUnderProjection e) y) (boundary n).ι
      (sliceUnderRestrict e i) (b ≫ vertexFiberι (sliceUnderProjection (i ≫ e)) y) := by
    constructor
    have he := congrArg (fun t ↦ t ≫ vertexFiberι (sliceUnderProjection (i ≫ e)) y) sq.w
    simpa only [cosliceRestrictionFiberMap, Category.assoc, vertexFiberMap_ι] using he
  have hbase : hs.lift ≫ sliceUnderProjection e = SSet.const y := by
    calc
      _ = hs.lift ≫ (sliceUnderRestrict e i ≫ sliceUnderProjection (i ≫ e)) :=
        congrArg (fun t ↦ hs.lift ≫ t) (sliceUnderRestrict_projection e i).symm
      _ = (hs.lift ≫ sliceUnderRestrict e i) ≫ sliceUnderProjection (i ≫ e) :=
        (Category.assoc _ _ _).symm
      _ = _ := by
        rw [hs.fac_right, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  refine CommSq.HasLift.mk' {
    l := vertexFiberLift (sliceUnderProjection e) y hs.lift hbase
    fac_left := ?_
    fac_right := ?_ }
  · apply vertexFiber_hom_ext
    rw [Category.assoc, vertexFiberLift_ι]
    exact hs.fac_left
  · apply vertexFiber_hom_ext
    exact hs.fac_right

/-- 概要：固定辺の終点への coslice の制限は trivial Kan fibration。
方針：終点包含の right anodyne 性を部分複体の表示へ移して充填する。
規約：標的 X は quasicategory。
使われ方：Kerodon Proposition 5.1.3.11、三角形から終点側の辺への射影。 -/
lemma sliceUnderRestrict_target_trivialKanFibration {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) :
    TrivialKanFibration (sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2))) := by
  let A : (Δ[1] : SSet.{u}).Subcomplex := stdSimplex.face {(0 : Fin 2)}ᶜ
  have hA : rightAnodyneExtensions A.ι := by
    rw [← rightAnodyneExtensions.cancel_left_of_respectsIso
      (stdSimplex.faceSingletonComplIso (0 : Fin 2)).hom]
    rw [stdSimplex.faceSingletonComplIso_hom_ι]
    exact endpointInclusion_rightAnodyne
  have := sliceUnderRestrict_trivialKanFibration_of_rightAnodyne e A hA
  have h := sliceUnderRestrict_trivialKanFibration_subcomplexIso e A
    (stdSimplex.faceSingletonComplIso (0 : Fin 2))
  simpa only [A, stdSimplex.faceSingletonComplIso_hom_ι] using h

/-- 概要：終点を固定した三角形の空間から終点側の写像空間への射影は trivial Kan fibration。
方針：終点への coslice 制限の充填性をその fiber へ移す。
規約：cocartesian 性や基底の射影は不要。
使われ方：Kerodon Proposition 5.1.3.11、Proposition 5.1.6.7、transport による写像空間の比較。 -/
lemma cosliceTriangleTarget_trivialKanFibration {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) (y : X _⦋0⦌) :
    TrivialKanFibration (cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y) := by
  have := sliceUnderRestrict_target_trivialKanFibration e
  exact cosliceRestrictionFiberMap_trivialKanFibration e _ y

end SerrePositivity.InfinityCategories
